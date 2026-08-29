/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Ideal

/-!
# Ideal operations for Lie algebras

Given a Lie module `M` over a Lie algebra `L`, there is a natural action of the Lie ideals of `L`
on the Lie submodules of `M`. In the special case that `M = L` with the adjoint action, this
provides a pairing of Lie ideals which is especially important. For example, it can be used to
define solvability / nilpotency of a Lie algebra via the derived / lower-central series.

## Main definitions

  * `LieSubmodule.hasBracket`
  * `LieSubmodule.lieIdeal_oper_eq_linear_span`
  * `LieIdeal.map_bracket_le`
  * `LieIdeal.comap_bracket_le`

## Notation

Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M` and a Lie
ideal `I ⊆ L`, we introduce the notation `⁅I, N⁆` for the Lie submodule of `M` corresponding to
the action defined in this file.

## Tags

lie algebra, ideal operation
-/

public section


universe u v w w₁ w₂

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]
variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)
variable (f : M ->ₗ⁅R,L⁆ M₂)

section LieIdealOperations

/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  statement: map f (comap f N₂) <= N₂
  proof: (N₂ : Set M₂).image_preimage_subset f

中文:
定理 map_comap_le
  结论: map f (comap f N₂) <= N₂
  证明: (N₂ : Set M₂).image_preimage_subset f

Depends on / 依赖: image_preimage_subset
-/
theorem map_comap_le : map f (comap f N₂) <= N₂ :=
  (N₂ : Set M₂).image_preimage_subset f

/--
theorem `map_comap_eq` / 定理 `map_comap_eq`

English:
theorem map_comap_eq
  given: (hf : N₂ <= f.range)
  statement: map f (comap f N₂) = N₂
  proof: by
  rw [SetLike.ext'_iff]
  exact Set.image_preimage_eq_of_subset hf

中文:
定理 map_comap_eq
  条件: (hf : N₂ <= f.range)
  结论: map f (comap f N₂) = N₂
  证明: by
  rw [SetLike.ext'_iff]
  exact Set.image_preimage_eq_of_subset hf

Depends on / 依赖: Set.image_preimage_eq_of_subset, SetLike, SetLike.ext, _iff, image_preimage_eq_of_subset
-/
theorem map_comap_eq (hf : N₂ <= f.range) : map f (comap f N₂) = N₂ := by
  rw [SetLike.ext'_iff]
  exact Set.image_preimage_eq_of_subset hf

/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  statement: N <= comap f (map f N)
  proof: (N : Set M).subset_preimage_image f

中文:
定理 le_comap_map
  结论: N <= comap f (map f N)
  证明: (N : Set M).subset_preimage_image f

Depends on / 依赖: subset_preimage_image
-/
theorem le_comap_map : N <= comap f (map f N) :=
  (N : Set M).subset_preimage_image f

/--
theorem `comap_map_eq` / 定理 `comap_map_eq`

English:
theorem comap_map_eq
  given: (hf : f.ker = ⊥)
  statement: comap f (map f N) = N
  proof: by
  rw [SetLike.ext'_iff]
  exact (N : Set M).preimage_image_eq (f.ker_eq_bot.mp hf)

@[simp]

中文:
定理 comap_map_eq
  条件: (hf : f.ker = ⊥)
  结论: comap f (map f N) = N
  证明: by
  rw [SetLike.ext'_iff]
  exact (N : Set M).preimage_image_eq (f.ker_eq_bot.mp hf)

@[simp]

Depends on / 依赖: SetLike, SetLike.ext, _iff, f.ker_eq_bot.mp, ker_eq_bot, preimage_image_eq
-/
theorem comap_map_eq (hf : f.ker = ⊥) : comap f (map f N) = N := by
  rw [SetLike.ext'_iff]
  exact (N : Set M).preimage_image_eq (f.ker_eq_bot.mp hf)

@[simp]
/--
theorem `map_comap_incl` / 定理 `map_comap_incl`

English:
theorem map_comap_incl
  statement: map N.incl (comap N.incl N') = N ⊓ N'
  proof: by
  rw [← toSubmodule_inj]
  exact (N : Submodule R M).map_comap_subtype N'

中文:
定理 map_comap_incl
  结论: map N.incl (comap N.incl N') = N ⊓ N'
  证明: by
  rw [← toSubmodule_inj]
  exact (N : Submodule R M).map_comap_subtype N'

Depends on / 依赖: Submodule, map_comap_subtype, toSubmodule_inj
-/
theorem map_comap_incl : map N.incl (comap N.incl N') = N ⊓ N' := by
  rw [← toSubmodule_inj]
  exact (N : Submodule R M).map_comap_subtype N'

variable [LieAlgebra R L] [LieModule R L M₂] (I J : LieIdeal R L)

/--
Instance `hasBracket` / 实例 `hasBracket`

English:
instance hasBracket
  signature: : Bracket (LieIdeal R L) (LieSubmodule R L M)
  body: ⟨fun I N => lieSpan R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }⟩

中文:
实例 hasBracket
  签名: : Bracket (LieIdeal R L) (Lie子模 R L M)
  定义体: ⟨fun I N => lieSpan R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }⟩

Depends on / 依赖: lieSpan
-/
instance hasBracket : Bracket (LieIdeal R L) (LieSubmodule R L M) :=
  ⟨fun I N => lieSpan R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }⟩

/--
theorem `lieIdeal_oper_eq_span` / 定理 `lieIdeal_oper_eq_span`

English:
theorem lieIdeal_oper_eq_span
  proof: rfl

中文:
定理 lieIdeal_oper_eq_span
  证明: rfl
-/
theorem lieIdeal_oper_eq_span :
    ⁅I, N⁆ = lieSpan R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) } :=
  rfl

/--
theorem `lieIdeal_oper_eq_linear_span` / 定理 `lieIdeal_oper_eq_linear_span`

English:
theorem lieIdeal_oper_eq_linear_span
  given: [LieModule R L M]
  proof: by
  apply le_antisymm
  · let s := { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
    have aux : forall (y : L), forall m' in Submodule.span R s, ⁅y, m'⁆ in Submodule.span R s := by
      intro y m' hm'
      refine Submodule.span_induction (R := R) (M := M) (s := s)
        (p := fun m' _ => ⁅y, m'⁆ in 

中文:
定理 lieIdeal_oper_eq_linear_span
  条件: [Lie模 R L M]
  证明: by
  apply le_antisymm
  · let s := { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
    have aux : forall (y : L), forall m' in Submodule.span R s, ⁅y, m'⁆ in Submodule.span R s := by
      intro y m' hm'
      refine Submodule.span_induction (R := R) (M := M) (s := s)
        (p := fun m' _ => ⁅y, m'⁆ in 

Depends on / 依赖: I.lie_mem, N.lie_mem, Submodule, Submodule.add_mem, Submodule.span, Submodule.span_induction, Submodule.subset_span, add_mem, le_antisymm, leibniz_lie, lie_mem, n.pro, property, span_induction, subset_span, x.property
-/
theorem lieIdeal_oper_eq_linear_span [LieModule R L M] :
    (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) } := by
  apply le_antisymm
  · let s := { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
    have aux : forall (y : L), forall m' in Submodule.span R s, ⁅y, m'⁆ in Submodule.span R s := by
      intro y m' hm'
      refine Submodule.span_induction (R := R) (M := M) (s := s)
        (p := fun m' _ => ⁅y, m'⁆ in Submodule.span R s) ?_ ?_ ?_ ?_ hm'
      · rintro m'' ⟨x, n, hm''⟩; rw [← hm'', leibniz_lie]
        refine Submodule.add_mem _ ?_ ?_ <;> apply Submodule.subset_span
        · use ⟨⁅y, ↑x⁆, I.lie_mem x.property⟩, n
        · use x, ⟨⁅y, ↑n⁆, N.lie_mem n.property⟩
      · simp
      · intro m₁ m₂ _ _ hm₁ hm₂; rw [lie_add]; exact Submodule.add_mem _ hm₁ hm₂
      · intro t m'' _ hm''; rw [lie_smul]; exact Submodule.smul_mem _ t hm''
    change _ <= ({ Submodule.span R s with lie_mem := fun hm' => aux _ _ hm' } : LieSubmodule R L M)
    rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]
    exact Submodule.subset_span
  · rw [lieIdeal_oper_eq_span]; apply submodule_span_le_lieSpan

/--
theorem `lieIdeal_oper_eq_linear_span'` / 定理 `lieIdeal_oper_eq_linear_span'`

English:
theorem lieIdeal_oper_eq_linear_span'
  given: [LieModule R L M]
  proof: by
  rw [lieIdeal_oper_eq_linear_span]
  congr
  ext m
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩
    exact ⟨x, hx, n, hn, rfl⟩
  · rintro ⟨x, hx, n, hn, rfl⟩
    exact ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩

中文:
定理 lieIdeal_oper_eq_linear_span'
  条件: [Lie模 R L M]
  证明: by
  rw [lieIdeal_oper_eq_linear_span]
  congr
  ext m
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩
    exact ⟨x, hx, n, hn, rfl⟩
  · rintro ⟨x, hx, n, hn, rfl⟩
    exact ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩

Depends on / 依赖: lieIdeal_oper_eq_linear_span
-/
theorem lieIdeal_oper_eq_linear_span' [LieModule R L M] :
    (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x in I) (n in N) } := by
  rw [lieIdeal_oper_eq_linear_span]
  congr
  ext m
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩
    exact ⟨x, hx, n, hn, rfl⟩
  · rintro ⟨x, hx, n, hn, rfl⟩
    exact ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩

/--
theorem `lie_le_iff` / 定理 `lie_le_iff`

English:
theorem lie_le_iff
  statement: ⁅I, N⁆ <= N' ↔ forall x in I, forall m in N, ⁅x, m⁆ in N'
  proof: by
  rw [lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  refine ⟨fun h x hx m hm => h ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h _ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩
  exact h x hx m hm

中文:
定理 lie_le_iff
  结论: ⁅I, N⁆ <= N' ↔ 对任意 x in I, 对任意 m in N, ⁅x, m⁆ in N'
  证明: by
  rw [lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  refine ⟨fun h x hx m hm => h ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h _ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩
  exact h x hx m hm

Depends on / 依赖: LieSubmodule, LieSubmodule.lieSpan_le, lieIdeal_oper_eq_span, lieSpan_le
-/
theorem lie_le_iff : ⁅I, N⁆ <= N' ↔ forall x in I, forall m in N, ⁅x, m⁆ in N' := by
  rw [lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  refine ⟨fun h x hx m hm => h ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h _ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩
  exact h x hx m hm

variable {N I} in
/--
theorem `lie_coe_mem_lie` / 定理 `lie_coe_mem_lie`

English:
theorem lie_coe_mem_lie
  given: (x : I) (m : N)
  statement: ⁅(x : L), (m : M)⁆ in ⁅I, N⁆
  proof: by
  rw [lieIdeal_oper_eq_span]; apply subset_lieSpan; use x, m

中文:
定理 lie_coe_mem_lie
  条件: (x : I) (m : N)
  结论: ⁅(x : L), (m : M)⁆ in ⁅I, N⁆
  证明: by
  rw [lieIdeal_oper_eq_span]; apply subset_lieSpan; use x, m

Depends on / 依赖: lieIdeal_oper_eq_span, subset_lieSpan
-/
theorem lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L), (m : M)⁆ in ⁅I, N⁆ := by
  rw [lieIdeal_oper_eq_span]; apply subset_lieSpan; use x, m

variable {N I} in
/--
theorem `lie_mem_lie` / 定理 `lie_mem_lie`

English:
theorem lie_mem_lie
  given: {x : L} {m : M} (hx : x in I) (hm : m in N)
  statement: ⁅x, m⁆ in ⁅I, N⁆
  proof: lie_coe_mem_lie ⟨x, hx⟩ ⟨m, hm⟩

中文:
定理 lie_mem_lie
  条件: {x : L} {m : M} (hx : x in I) (hm : m in N)
  结论: ⁅x, m⁆ in ⁅I, N⁆
  证明: lie_coe_mem_lie ⟨x, hx⟩ ⟨m, hm⟩

Depends on / 依赖: lie_coe_mem_lie
-/
theorem lie_mem_lie {x : L} {m : M} (hx : x in I) (hm : m in N) : ⁅x, m⁆ in ⁅I, N⁆ :=
  lie_coe_mem_lie ⟨x, hx⟩ ⟨m, hm⟩

/--
theorem `lie_comm` / 定理 `lie_comm`

English:
theorem lie_comm
  statement: ⁅I, J⁆ = ⁅J, I⁆
  proof: by
  suffices forall I J : LieIdeal R L, ⁅I, J⁆ <= ⁅J, I⁆ by exact le_antisymm (this I J) (this J I)
  clear! I J; intro I J
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]; rintro x ⟨y, z, h⟩; rw [← h]
  rw [← lie_skew]; rw [← lie_neg]; rw [← LieSubmodule.coe_neg]
  apply lie_coe_mem_lie

中文:
定理 lie_comm
  结论: ⁅I, J⁆ = ⁅J, I⁆
  证明: by
  suffices forall I J : LieIdeal R L, ⁅I, J⁆ <= ⁅J, I⁆ by exact le_antisymm (this I J) (this J I)
  clear! I J; intro I J
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]; rintro x ⟨y, z, h⟩; rw [← h]
  rw [← lie_skew]; rw [← lie_neg]; rw [← LieSubmodule.coe_neg]
  apply lie_coe_mem_lie

Depends on / 依赖: LieIdeal, LieSubmodule, LieSubmodule.coe_neg, coe_neg, le_antisymm, lieIdeal_oper_eq_span, lieSpan_le, lie_coe_mem_lie, lie_neg, lie_skew
-/
theorem lie_comm : ⁅I, J⁆ = ⁅J, I⁆ := by
  suffices forall I J : LieIdeal R L, ⁅I, J⁆ <= ⁅J, I⁆ by exact le_antisymm (this I J) (this J I)
  clear! I J; intro I J
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]; rintro x ⟨y, z, h⟩; rw [← h]
  rw [← lie_skew]; rw [← lie_neg]; rw [← LieSubmodule.coe_neg]
  apply lie_coe_mem_lie

/--
theorem `lie_le_right` / 定理 `lie_le_right`

English:
theorem lie_le_right
  statement: ⁅I, N⁆ <= N
  proof: by
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]; rintro m ⟨x, n, hn⟩; rw [← hn]
  exact N.lie_mem n.property

中文:
定理 lie_le_right
  结论: ⁅I, N⁆ <= N
  证明: by
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]; rintro m ⟨x, n, hn⟩; rw [← hn]
  exact N.lie_mem n.property

Depends on / 依赖: N.lie_mem, lieIdeal_oper_eq_span, lieSpan_le, lie_mem, n.property, property
-/
theorem lie_le_right : ⁅I, N⁆ <= N := by
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]; rintro m ⟨x, n, hn⟩; rw [← hn]
  exact N.lie_mem n.property

/--
theorem `lie_le_left` / 定理 `lie_le_left`

English:
theorem lie_le_left
  statement: ⁅I, J⁆ <= I
  proof: by rw [lie_comm]; exact lie_le_right I J

中文:
定理 lie_le_left
  结论: ⁅I, J⁆ <= I
  证明: by rw [lie_comm]; exact lie_le_right I J

Depends on / 依赖: lie_comm, lie_le_right
-/
theorem lie_le_left : ⁅I, J⁆ <= I := by rw [lie_comm]; exact lie_le_right I J

/--
theorem `lie_le_inf` / 定理 `lie_le_inf`

English:
theorem lie_le_inf
  statement: ⁅I, J⁆ <= I ⊓ J
  proof: by rw [le_inf_iff]; exact ⟨lie_le_left I J, lie_le_right J I⟩

@[simp]

中文:
定理 lie_le_inf
  结论: ⁅I, J⁆ <= I ⊓ J
  证明: by rw [le_inf_iff]; exact ⟨lie_le_left I J, lie_le_right J I⟩

@[simp]

Depends on / 依赖: le_inf_iff, lie_le_left, lie_le_right
-/
theorem lie_le_inf : ⁅I, J⁆ <= I ⊓ J := by rw [le_inf_iff]; exact ⟨lie_le_left I J, lie_le_right J I⟩

@[simp]
/--
theorem `lie_bot` / 定理 `lie_bot`

English:
theorem lie_bot
  statement: ⁅I, (⊥ : LieSubmodule R L M)⁆ = ⊥
  proof: by rw [eq_bot_iff]; apply lie_le_right

@[simp]

中文:
定理 lie_bot
  结论: ⁅I, (⊥ : Lie子模 R L M)⁆ = ⊥
  证明: by rw [eq_bot_iff]; apply lie_le_right

@[simp]

Depends on / 依赖: eq_bot_iff, lie_le_right
-/
theorem lie_bot : ⁅I, (⊥ : LieSubmodule R L M)⁆ = ⊥ := by rw [eq_bot_iff]; apply lie_le_right

@[simp]
/--
theorem `bot_lie` / 定理 `bot_lie`

English:
theorem bot_lie
  statement: ⁅(⊥ : LieIdeal R L), N⁆ = ⊥
  proof: by
  suffices ⁅(⊥ : LieIdeal R L), N⁆ <= ⊥ by exact le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]; rintro m ⟨⟨x, hx⟩, n, hn⟩; rw [← hn]
  change x in (⊥ : LieIdeal R L) at hx; rw [mem_bot] at hx; simp [hx]

中文:
定理 bot_lie
  结论: ⁅(⊥ : LieIdeal R L), N⁆ = ⊥
  证明: by
  suffices ⁅(⊥ : LieIdeal R L), N⁆ <= ⊥ by exact le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]; rintro m ⟨⟨x, hx⟩, n, hn⟩; rw [← hn]
  change x in (⊥ : LieIdeal R L) at hx; rw [mem_bot] at hx; simp [hx]

Depends on / 依赖: LieIdeal, le_bot_iff, le_bot_iff.mp, lieIdeal_oper_eq_span, lieSpan_le, mem_bot
-/
theorem bot_lie : ⁅(⊥ : LieIdeal R L), N⁆ = ⊥ := by
  suffices ⁅(⊥ : LieIdeal R L), N⁆ <= ⊥ by exact le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]; rintro m ⟨⟨x, hx⟩, n, hn⟩; rw [← hn]
  change x in (⊥ : LieIdeal R L) at hx; rw [mem_bot] at hx; simp [hx]

/--
theorem `lie_eq_bot_iff` / 定理 `lie_eq_bot_iff`

English:
theorem lie_eq_bot_iff
  statement: ⁅I, N⁆ = ⊥ ↔ forall x in I, forall m in N, ⁅(x : L), m⁆ = 0
  proof: by
  rw [lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_eq_bot_iff]
  refine ⟨fun h x hx m hm => h ⁅x, m⁆ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h - ⟨⟨x, hx⟩, ⟨⟨n, hn⟩, rfl⟩⟩
  exact h x hx n hn

中文:
定理 lie_eq_bot_iff
  结论: ⁅I, N⁆ = ⊥ ↔ 对任意 x in I, 对任意 m in N, ⁅(x : L), m⁆ = 0
  证明: by
  rw [lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_eq_bot_iff]
  refine ⟨fun h x hx m hm => h ⁅x, m⁆ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h - ⟨⟨x, hx⟩, ⟨⟨n, hn⟩, rfl⟩⟩
  exact h x hx n hn

Depends on / 依赖: LieSubmodule, LieSubmodule.lieSpan_eq_bot_iff, lieIdeal_oper_eq_span, lieSpan_eq_bot_iff
-/
theorem lie_eq_bot_iff : ⁅I, N⁆ = ⊥ ↔ forall x in I, forall m in N, ⁅(x : L), m⁆ = 0 := by
  rw [lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_eq_bot_iff]
  refine ⟨fun h x hx m hm => h ⁅x, m⁆ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h - ⟨⟨x, hx⟩, ⟨⟨n, hn⟩, rfl⟩⟩
  exact h x hx n hn

variable {I J N N'} in
@[gcongr]
/--
theorem `mono_lie` / 定理 `mono_lie`

English:
theorem mono_lie
  given: (h₁ : I <= J) (h₂ : N <= N')
  statement: ⁅I, N⁆ <= ⁅J, N'⁆
  proof: by
  intro m h
  rw [lieIdeal_oper_eq_span]; rw [mem_lieSpan] at h; rw [lieIdeal_oper_eq_span, mem_lieSpan]
  intro N hN; apply h; rintro m' ⟨⟨x, hx⟩, ⟨n, hn⟩, hm⟩; rw [← hm]; apply hN
  use ⟨x, h₁ hx⟩, ⟨n, h₂ hn⟩

中文:
定理 mono_lie
  条件: (h₁ : I <= J) (h₂ : N <= N')
  结论: ⁅I, N⁆ <= ⁅J, N'⁆
  证明: by
  intro m h
  rw [lieIdeal_oper_eq_span]; rw [mem_lieSpan] at h; rw [lieIdeal_oper_eq_span, mem_lieSpan]
  intro N hN; apply h; rintro m' ⟨⟨x, hx⟩, ⟨n, hn⟩, hm⟩; rw [← hm]; apply hN
  use ⟨x, h₁ hx⟩, ⟨n, h₂ hn⟩

Depends on / 依赖: lieIdeal_oper_eq_span, mem_lieSpan
-/
theorem mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <= ⁅J, N'⁆ := by
  intro m h
  rw [lieIdeal_oper_eq_span]; rw [mem_lieSpan] at h; rw [lieIdeal_oper_eq_span, mem_lieSpan]
  intro N hN; apply h; rintro m' ⟨⟨x, hx⟩, ⟨n, hn⟩, hm⟩; rw [← hm]; apply hN
  use ⟨x, h₁ hx⟩, ⟨n, h₂ hn⟩

variable {I J} in
/--
theorem `mono_lie_left` / 定理 `mono_lie_left`

English:
theorem mono_lie_left
  given: (h : I <= J)
  statement: ⁅I, N⁆ <= ⁅J, N⁆
  proof: mono_lie h (le_refl N)

中文:
定理 mono_lie_left
  条件: (h : I <= J)
  结论: ⁅I, N⁆ <= ⁅J, N⁆
  证明: mono_lie h (le_refl N)

Depends on / 依赖: le_refl, mono_lie
-/
theorem mono_lie_left (h : I <= J) : ⁅I, N⁆ <= ⁅J, N⁆ :=
  mono_lie h (le_refl N)

variable {N N'} in
/--
theorem `mono_lie_right` / 定理 `mono_lie_right`

English:
theorem mono_lie_right
  given: (h : N <= N')
  statement: ⁅I, N⁆ <= ⁅I, N'⁆
  proof: mono_lie (le_refl I) h

@[simp]

中文:
定理 mono_lie_right
  条件: (h : N <= N')
  结论: ⁅I, N⁆ <= ⁅I, N'⁆
  证明: mono_lie (le_refl I) h

@[simp]

Depends on / 依赖: le_refl, mono_lie
-/
theorem mono_lie_right (h : N <= N') : ⁅I, N⁆ <= ⁅I, N'⁆ :=
  mono_lie (le_refl I) h

@[simp]
/--
theorem `lie_sup` / 定理 `lie_sup`

English:
theorem lie_sup
  statement: ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆
  proof: by
  have h : ⁅I, N⁆ ⊔ ⁅I, N'⁆ <= ⁅I, N ⊔ N'⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply mono_lie_right <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I, N ⊔ N'⁆ <= ⁅I, N⁆ ⊔ ⁅I, N'⁆ by exact le_antisymm this h
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]
  rintro m ⟨x, ⟨n, hn⟩, h

中文:
定理 lie_sup
  结论: ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆
  证明: by
  have h : ⁅I, N⁆ ⊔ ⁅I, N'⁆ <= ⁅I, N ⊔ N'⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply mono_lie_right <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I, N ⊔ N'⁆ <= ⁅I, N⁆ ⊔ ⁅I, N'⁆ by exact le_antisymm this h
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]
  rintro m ⟨x, ⟨n, hn⟩, h

Depends on / 依赖: LieSubmodule, LieSubmodule.mem_sup, SetLike, SetLike.mem_coe, le_antisymm, le_sup_left, le_sup_right, lieIdeal_oper_eq_span, lieSpan_le, lie_coe_mem_lie, mem_coe, mem_sup, mono_lie_right, sup_le_iff
-/
theorem lie_sup : ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆ := by
  have h : ⁅I, N⁆ ⊔ ⁅I, N'⁆ <= ⁅I, N ⊔ N'⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply mono_lie_right <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I, N ⊔ N'⁆ <= ⁅I, N⁆ ⊔ ⁅I, N'⁆ by exact le_antisymm this h
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]
  rintro m ⟨x, ⟨n, hn⟩, h⟩
  simp only [SetLike.mem_coe]
  rw [LieSubmodule.mem_sup] at hn ⊢
  rcases hn with ⟨n₁, hn₁, n₂, hn₂, hn'⟩
  use ⁅(x : L), (⟨n₁, hn₁⟩ : N)⁆; constructor; · apply lie_coe_mem_lie
  use ⁅(x : L), (⟨n₂, hn₂⟩ : N')⁆; constructor; · apply lie_coe_mem_lie
  simp [← h, ← hn']

@[simp]
/--
theorem `sup_lie` / 定理 `sup_lie`

English:
theorem sup_lie
  statement: ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆
  proof: by
  have h : ⁅I, N⁆ ⊔ ⁅J, N⁆ <= ⁅I ⊔ J, N⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply mono_lie_left <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I ⊔ J, N⁆ <= ⁅I, N⁆ ⊔ ⁅J, N⁆ by exact le_antisymm this h
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]
  rintro m ⟨⟨x, hx⟩, n, h⟩
  s

中文:
定理 sup_lie
  结论: ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆
  证明: by
  have h : ⁅I, N⁆ ⊔ ⁅J, N⁆ <= ⁅I ⊔ J, N⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply mono_lie_left <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I ⊔ J, N⁆ <= ⁅I, N⁆ ⊔ ⁅J, N⁆ by exact le_antisymm this h
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]
  rintro m ⟨⟨x, hx⟩, n, h⟩
  s

Depends on / 依赖: LieSubmodule, LieSubmodule.mem_sup, SetLike, SetLike.mem_coe, le_antisymm, le_sup_left, le_sup_right, lieIdeal_oper_eq_span, lieSpan_le, lie_coe_mem_lie, mem_coe, mem_sup, mono_lie_left, sup_le_iff
-/
theorem sup_lie : ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆ := by
  have h : ⁅I, N⁆ ⊔ ⁅J, N⁆ <= ⁅I ⊔ J, N⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply mono_lie_left <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I ⊔ J, N⁆ <= ⁅I, N⁆ ⊔ ⁅J, N⁆ by exact le_antisymm this h
  rw [lieIdeal_oper_eq_span]; rw [lieSpan_le]
  rintro m ⟨⟨x, hx⟩, n, h⟩
  simp only [SetLike.mem_coe]
  rw [LieSubmodule.mem_sup] at hx ⊢
  rcases hx with ⟨x₁, hx₁, x₂, hx₂, hx'⟩
  use ⁅((⟨x₁, hx₁⟩ : I) : L), (n : N)⁆; constructor; · apply lie_coe_mem_lie
  use ⁅((⟨x₂, hx₂⟩ : J) : L), (n : N)⁆; constructor; · apply lie_coe_mem_lie
  simp [← h, ← hx']

/--
theorem `lie_inf` / 定理 `lie_inf`

English:
theorem lie_inf
  statement: ⁅I, N ⊓ N'⁆ <= ⁅I, N⁆ ⊓ ⁅I, N'⁆
  proof: by
  rw [le_inf_iff]; constructor <;>
  apply mono_lie_right <;> [exact inf_le_left; exact inf_le_right]

中文:
定理 lie_inf
  结论: ⁅I, N ⊓ N'⁆ <= ⁅I, N⁆ ⊓ ⁅I, N'⁆
  证明: by
  rw [le_inf_iff]; constructor <;>
  apply mono_lie_right <;> [exact inf_le_left; exact inf_le_right]

Depends on / 依赖: inf_le_left, inf_le_right, le_inf_iff, mono_lie_right
-/
theorem lie_inf : ⁅I, N ⊓ N'⁆ <= ⁅I, N⁆ ⊓ ⁅I, N'⁆ := by
  rw [le_inf_iff]; constructor <;>
  apply mono_lie_right <;> [exact inf_le_left; exact inf_le_right]

/--
theorem `inf_lie` / 定理 `inf_lie`

English:
theorem inf_lie
  statement: ⁅I ⊓ J, N⁆ <= ⁅I, N⁆ ⊓ ⁅J, N⁆
  proof: by
  rw [le_inf_iff]; constructor <;>
  apply mono_lie_left <;> [exact inf_le_left; exact inf_le_right]

中文:
定理 inf_lie
  结论: ⁅I ⊓ J, N⁆ <= ⁅I, N⁆ ⊓ ⁅J, N⁆
  证明: by
  rw [le_inf_iff]; constructor <;>
  apply mono_lie_left <;> [exact inf_le_left; exact inf_le_right]

Depends on / 依赖: inf_le_left, inf_le_right, le_inf_iff, mono_lie_left
-/
theorem inf_lie : ⁅I ⊓ J, N⁆ <= ⁅I, N⁆ ⊓ ⁅J, N⁆ := by
  rw [le_inf_iff]; constructor <;>
  apply mono_lie_left <;> [exact inf_le_left; exact inf_le_right]

/--
theorem `map_bracket_eq` / 定理 `map_bracket_eq`

English:
theorem map_bracket_eq
  given: [LieModule R L M]
  statement: map f ⁅I, N⁆ = ⁅I, map f N⁆
  proof: by
  rw [← toSubmodule_inj]; rw [toSubmodule_map]; rw [lieIdeal_oper_eq_linear_span]; rw [lieIdeal_oper_eq_linear_span]; rw [Submodule.map_span]
  congr
  ext m
  simp

中文:
定理 map_bracket_eq
  条件: [Lie模 R L M]
  结论: map f ⁅I, N⁆ = ⁅I, map f N⁆
  证明: by
  rw [← toSubmodule_inj]; rw [toSubmodule_map]; rw [lieIdeal_oper_eq_linear_span]; rw [lieIdeal_oper_eq_linear_span]; rw [Submodule.map_span]
  congr
  ext m
  simp

Depends on / 依赖: Submodule, Submodule.map_span, lieIdeal_oper_eq_linear_span, map_span, toSubmodule_inj, toSubmodule_map
-/
theorem map_bracket_eq [LieModule R L M] : map f ⁅I, N⁆ = ⁅I, map f N⁆ := by
  rw [← toSubmodule_inj]; rw [toSubmodule_map]; rw [lieIdeal_oper_eq_linear_span]; rw [lieIdeal_oper_eq_linear_span]; rw [Submodule.map_span]
  congr
  ext m
  simp

/--
theorem `comap_bracket_eq` / 定理 `comap_bracket_eq`

English:
theorem comap_bracket_eq
  given: [LieModule R L M] (hf₁ : f.ker = ⊥) (hf₂ : N₂ <= f.range)
  proof: by
  conv_lhs => rw [← map_comap_eq N₂ f hf₂]
  rw [← map_bracket_eq]; rw [comap_map_eq _ f hf₁]

中文:
定理 comap_bracket_eq
  条件: [Lie模 R L M] (hf₁ : f.ker = ⊥) (hf₂ : N₂ <= f.range)
  证明: by
  conv_lhs => rw [← map_comap_eq N₂ f hf₂]
  rw [← map_bracket_eq]; rw [comap_map_eq _ f hf₁]

Depends on / 依赖: comap_map_eq, conv_lhs, map_bracket_eq, map_comap_eq
-/
theorem comap_bracket_eq [LieModule R L M] (hf₁ : f.ker = ⊥) (hf₂ : N₂ <= f.range) :
    comap f ⁅I, N₂⁆ = ⁅I, comap f N₂⁆ := by
  conv_lhs => rw [← map_comap_eq N₂ f hf₂]
  rw [← map_bracket_eq]; rw [comap_map_eq _ f hf₁]

end LieIdealOperations

end LieSubmodule

namespace LieIdeal

open LieAlgebra

variable {R : Type u} {L : Type v} {L' : Type w₂}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (f : L ->ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

/--
theorem `map_bracket_le` / 定理 `map_bracket_le`

English:
theorem map_bracket_le
  given: {I₁ I₂ : LieIdeal R L}
  statement: map f ⁅I₁, I₂⁆ <= ⁅map f I₁, map f I₂⁆
  proof: by
  rw [map_le_iff_le_comap]; rw [LieSubmodule.lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  intro x hx
  obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hx⟩ := hx
  rw [← hx]
  let fy₁ : ↥(map f I₁) := ⟨f y₁, mem_map hy₁⟩
  let fy₂ : ↥(map f I₂) := ⟨f y₂, mem_map hy₂⟩
  change _ in comap f ⁅map f I₁, map f

中文:
定理 map_bracket_le
  条件: {I₁ I₂ : LieIdeal R L}
  结论: map f ⁅I₁, I₂⁆ <= ⁅map f I₁, map f I₂⁆
  证明: by
  rw [map_le_iff_le_comap]; rw [LieSubmodule.lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  intro x hx
  obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hx⟩ := hx
  rw [← hx]
  let fy₁ : ↥(map f I₁) := ⟨f y₁, mem_map hy₁⟩
  let fy₂ : ↥(map f I₂) := ⟨f y₂, mem_map hy₂⟩
  change _ in comap f ⁅map f I₁, map f

Depends on / 依赖: LieHom, LieHom.map_lie, LieSubmodule, LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le, LieSubmodule.lie_coe_mem_lie, lieIdeal_oper_eq_span, lieSpan_le, lie_coe_mem_lie, map_le_iff_le_comap, map_lie, mem_comap, mem_map
-/
theorem map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅I₁, I₂⁆ <= ⁅map f I₁, map f I₂⁆ := by
  rw [map_le_iff_le_comap]; rw [LieSubmodule.lieIdeal_oper_eq_span]; rw [LieSubmodule.lieSpan_le]
  intro x hx
  obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hx⟩ := hx
  rw [← hx]
  let fy₁ : ↥(map f I₁) := ⟨f y₁, mem_map hy₁⟩
  let fy₂ : ↥(map f I₂) := ⟨f y₂, mem_map hy₂⟩
  change _ in comap f ⁅map f I₁, map f I₂⁆
  simp only [mem_comap, LieHom.map_lie]
  exact LieSubmodule.lie_coe_mem_lie fy₁ fy₂

/--
theorem `map_bracket_eq` / 定理 `map_bracket_eq`

English:
theorem map_bracket_eq
  given: {I₁ I₂ : LieIdeal R L} (h : Function.Surjective f)
  proof: by
  suffices ⁅map f I₁, map f I₂⁆ <= map f ⁅I₁, I₂⁆ by exact le_antisymm (map_bracket_le f) this
  rw [← LieSubmodule.toSubmodule_le_toSubmodule]; rw [coe_map_of_surjective h]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LinearMap.map_span]
  

中文:
定理 map_bracket_eq
  条件: {I₁ I₂ : LieIdeal R L} (h : 函数.满射 f)
  证明: by
  suffices ⁅map f I₁, map f I₂⁆ <= map f ⁅I₁, I₂⁆ by exact le_antisymm (map_bracket_le f) this
  rw [← LieSubmodule.toSubmodule_le_toSubmodule]; rw [coe_map_of_surjective h]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LinearMap.map_span]
  

Depends on / 依赖: LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.toSubmodule_le_toSubmodule, LinearMap, LinearMap.map_span, Submodule, Submodule.span_mono, coe_map_of_surjective, le_antisymm, lieIdeal_oper_eq_linear_span, map_bracket_le, map_span, mem_map_of_surjective, span_mono, toSubmodule_le_toSubmodule
-/
theorem map_bracket_eq {I₁ I₂ : LieIdeal R L} (h : Function.Surjective f) :
    map f ⁅I₁, I₂⁆ = ⁅map f I₁, map f I₂⁆ := by
  suffices ⁅map f I₁, map f I₂⁆ <= map f ⁅I₁, I₂⁆ by exact le_antisymm (map_bracket_le f) this
  rw [← LieSubmodule.toSubmodule_le_toSubmodule]; rw [coe_map_of_surjective h]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LinearMap.map_span]
  apply Submodule.span_mono
  rintro x ⟨⟨z₁, h₁⟩, ⟨z₂, h₂⟩, rfl⟩
  obtain ⟨y₁, rfl⟩ := mem_map_of_surjective h h₁
  obtain ⟨y₂, rfl⟩ := mem_map_of_surjective h h₂
  exact ⟨⁅(y₁ : L), (y₂ : L)⁆, ⟨y₁, y₂, rfl⟩, by apply f.map_lie⟩

/--
theorem `comap_bracket_le` / 定理 `comap_bracket_le`

English:
theorem comap_bracket_le
  given: {J₁ J₂ : LieIdeal R L'}
  statement: ⁅comap f J₁, comap f J₂⁆ <= comap f ⁅J₁, J₂⁆
  proof: by
  rw [← map_le_iff_le_comap]
  exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie map_comap_le map_comap_le)

中文:
定理 comap_bracket_le
  条件: {J₁ J₂ : LieIdeal R L'}
  结论: ⁅comap f J₁, comap f J₂⁆ <= comap f ⁅J₁, J₂⁆
  证明: by
  rw [← map_le_iff_le_comap]
  exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie map_comap_le map_comap_le)

Depends on / 依赖: LieSubmodule, LieSubmodule.mono_lie, le_trans, map_bracket_le, map_comap_le, map_le_iff_le_comap, mono_lie
-/
theorem comap_bracket_le {J₁ J₂ : LieIdeal R L'} : ⁅comap f J₁, comap f J₂⁆ <= comap f ⁅J₁, J₂⁆ := by
  rw [← map_le_iff_le_comap]
  exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie map_comap_le map_comap_le)

variable {f}

/--
theorem `map_comap_incl` / 定理 `map_comap_incl`

English:
theorem map_comap_incl
  given: {I₁ I₂ : LieIdeal R L}
  statement: map I₁.incl (comap I₁.incl I₂) = I₁ ⊓ I₂
  proof: by
  conv_rhs => rw [← I₁.incl_idealRange]
  rw [← map_comap_eq]
  exact I₁.incl_isIdealMorphism

中文:
定理 map_comap_incl
  条件: {I₁ I₂ : LieIdeal R L}
  结论: map I₁.incl (comap I₁.incl I₂) = I₁ ⊓ I₂
  证明: by
  conv_rhs => rw [← I₁.incl_idealRange]
  rw [← map_comap_eq]
  exact I₁.incl_isIdealMorphism

Depends on / 依赖: conv_rhs, incl_idealRange, incl_isIdealMorphism, map_comap_eq
-/
theorem map_comap_incl {I₁ I₂ : LieIdeal R L} : map I₁.incl (comap I₁.incl I₂) = I₁ ⊓ I₂ := by
  conv_rhs => rw [← I₁.incl_idealRange]
  rw [← map_comap_eq]
  exact I₁.incl_isIdealMorphism

/--
theorem `comap_bracket_eq` / 定理 `comap_bracket_eq`

English:
theorem comap_bracket_eq
  given: {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism)
  proof: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [comap_toSubmodule]; rw [LieSubmodule.sup_toSubmodule]; rw [f.ker_toSubmodule]; rw [← Submodule.comap_map_eq]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LinearMap.map_span]
  congr
  ext
  simp_all

中文:
定理 comap_bracket_eq
  条件: {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism)
  证明: by
  rw [← LieSubmodule.toSubmodule_inj]; rw [comap_toSubmodule]; rw [LieSubmodule.sup_toSubmodule]; rw [f.ker_toSubmodule]; rw [← Submodule.comap_map_eq]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LinearMap.map_span]
  congr
  ext
  simp_all

Depends on / 依赖: LieHom, LieHom.coe_toLinearMap, LieHom.map_lie, LieHom.mem_idealRange_iff, LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_inf, LieSubmodule.sup_toSubmodule, LieSubmodule.toSubmodule_inj, LinearMap, LinearMap.map_span, Set.mem_ofPred_eq, Submodule, Submodule.comap_map_eq, Subtype, Subtype.exists, coe_toLinearMap, comap_map_eq, comap_toSubmodule, exists_exists_and_exists_and_eq_and
-/
theorem comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) :
    comap f ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ = ⁅comap f J₁, comap f J₂⁆ ⊔ f.ker := by
  rw [← LieSubmodule.toSubmodule_inj]; rw [comap_toSubmodule]; rw [LieSubmodule.sup_toSubmodule]; rw [f.ker_toSubmodule]; rw [← Submodule.comap_map_eq]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span]; rw [LinearMap.map_span]
  congr
  ext
  simp_all only [Subtype.exists, LieSubmodule.mem_inf, LieHom.mem_idealRange_iff, exists_prop,
    Set.mem_ofPred_eq, LieHom.coe_toLinearMap, mem_comap,
    exists_exists_and_exists_and_eq_and, LieHom.map_lie]
  grind

/--
theorem `map_comap_bracket_eq` / 定理 `map_comap_bracket_eq`

English:
theorem map_comap_bracket_eq
  given: {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism)
  proof: by
  rw [← map_sup_ker_eq_map]; rw [← comap_bracket_eq h]; rw [map_comap_eq h]; rw [inf_eq_right]
  exact le_trans (LieSubmodule.lie_le_left _ _) inf_le_left

中文:
定理 map_comap_bracket_eq
  条件: {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism)
  证明: by
  rw [← map_sup_ker_eq_map]; rw [← comap_bracket_eq h]; rw [map_comap_eq h]; rw [inf_eq_right]
  exact le_trans (LieSubmodule.lie_le_left _ _) inf_le_left

Depends on / 依赖: LieSubmodule, LieSubmodule.lie_le_left, comap_bracket_eq, inf_eq_right, inf_le_left, le_trans, lie_le_left, map_comap_eq, map_sup_ker_eq_map
-/
theorem map_comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) :
    map f ⁅comap f J₁, comap f J₂⁆ = ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ := by
  rw [← map_sup_ker_eq_map]; rw [← comap_bracket_eq h]; rw [map_comap_eq h]; rw [inf_eq_right]
  exact le_trans (LieSubmodule.lie_le_left _ _) inf_le_left

/--
theorem `comap_bracket_incl` / 定理 `comap_bracket_incl`

English:
theorem comap_bracket_incl
  given: {I₁ I₂ : LieIdeal R L}
  proof: by
  conv_rhs =>
    congr
    next => skip
    rw [← I.incl_idealRange]
  rw [comap_bracket_eq]
  · simp
  · exact I.incl_isIdealMorphism

中文:
定理 comap_bracket_incl
  条件: {I₁ I₂ : LieIdeal R L}
  证明: by
  conv_rhs =>
    congr
    next => skip
    rw [← I.incl_idealRange]
  rw [comap_bracket_eq]
  · simp
  · exact I.incl_isIdealMorphism

Depends on / 依赖: I.incl_idealRange, I.incl_isIdealMorphism, comap_bracket_eq, conv_rhs, incl_idealRange, incl_isIdealMorphism
-/
theorem comap_bracket_incl {I₁ I₂ : LieIdeal R L} :
    ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I ⊓ I₁, I ⊓ I₂⁆ := by
  conv_rhs =>
    congr
    next => skip
    rw [← I.incl_idealRange]
  rw [comap_bracket_eq]
  · simp
  · exact I.incl_isIdealMorphism

/--
theorem `comap_bracket_incl_of_le` / 定理 `comap_bracket_incl_of_le`

English:
theorem comap_bracket_incl_of_le
  given: {I₁ I₂ : LieIdeal R L} (h₁ : I₁ <= I) (h₂ : I₂ <= I)
  proof: by
    rw [comap_bracket_incl]; rw [← inf_eq_right] at h₁ h₂; rw [h₁, h₂]

中文:
定理 comap_bracket_incl_of_le
  条件: {I₁ I₂ : LieIdeal R L} (h₁ : I₁ <= I) (h₂ : I₂ <= I)
  证明: by
    rw [comap_bracket_incl]; rw [← inf_eq_right] at h₁ h₂; rw [h₁, h₂]

Depends on / 依赖: comap_bracket_incl, inf_eq_right
-/
theorem comap_bracket_incl_of_le {I₁ I₂ : LieIdeal R L} (h₁ : I₁ <= I) (h₂ : I₂ <= I) :
    ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I₁, I₂⁆ := by
    rw [comap_bracket_incl]; rw [← inf_eq_right] at h₁ h₂; rw [h₁, h₂]

end LieIdeal
