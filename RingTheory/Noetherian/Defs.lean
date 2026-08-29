/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Noetherian rings and modules

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodules M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left-Noetherian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `IsNoetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `isNoetherian_iff` is the theorem that an R-module M is Noetherian iff `>` is well-founded on
  `Submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `RingTheory.Polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/

@[expose] public section

assert_not_exists Finsupp.linearCombination Matrix Pi.basis

open Set Pointwise

-- TODO: should this be renamed to `Noetherian`?
/--
Definition of `IsNoetherian` / `IsNoetherian` 的定义

English:
class IsNoetherian
  parameters: (R M) [Semiring R] [AddCommMonoid M] [Module R M]
  axioms and operations (1):
    - noetherian : forall s : Submodule R M, s.FG

中文:
类 是Noether
  参数: (R M) [半环 R] [加法交换幺半群 M] [模 R M]
  公理与运算 (1 个):
    - noetherian : 对任意 s : 子模 R M, s.FG
-/
class IsNoetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  noetherian : forall s : Submodule R M, s.FG

attribute [inherit_doc IsNoetherian] IsNoetherian.noetherian

section

variable {R : Type*} {M : Type*} {P : Type*}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid P]
variable [Module R M] [Module R P]

open IsNoetherian

/--
theorem `isNoetherian_def` / 定理 `isNoetherian_def`

English:
theorem isNoetherian_def
  statement: IsNoetherian R M ↔ forall s : Submodule R M, s.FG
  proof: ⟨fun h => h.noetherian, IsNoetherian.mk⟩

中文:
定理 isNoetherian_def
  结论: 是Noether R M ↔ 对任意 s : 子模 R M, s.FG
  证明: ⟨fun h => h.noetherian, IsNoetherian.mk⟩

Depends on / 依赖: IsNoetherian, IsNoetherian.mk, h.noetherian, noetherian
-/
theorem isNoetherian_def : IsNoetherian R M ↔ forall s : Submodule R M, s.FG :=
  ⟨fun h => h.noetherian, IsNoetherian.mk⟩

/--
theorem `isNoetherian_submodule` / 定理 `isNoetherian_submodule`

English:
theorem isNoetherian_submodule
  given: {N : Submodule R M}
  proof: by
  refine ⟨fun ⟨hn⟩ => fun s hs =>
    have : s <= LinearMap.range N.subtype := N.range_subtype.symm ▸ hs
    Submodule.map_comap_eq_self this ▸ (hn _).map _,
    fun h => ⟨fun s => ?_⟩⟩
  specialize h (s.map N.subtype) (Submodule.map_subtype_le N s)
  exact Submodule.fg_of_fg_map_injective N.subt

中文:
定理 isNoetherian_submodule
  条件: {N : 子模 R M}
  证明: by
  refine ⟨fun ⟨hn⟩ => fun s hs =>
    have : s <= LinearMap.range N.subtype := N.range_subtype.symm ▸ hs
    Submodule.map_comap_eq_self this ▸ (hn _).map _,
    fun h => ⟨fun s => ?_⟩⟩
  specialize h (s.map N.subtype) (Submodule.map_subtype_le N s)
  exact Submodule.fg_of_fg_map_injective N.subt

Depends on / 依赖: LinearMap, LinearMap.range, N.range_subtype.symm, N.subtype, Submodule, Submodule.fg_of_fg_map_injective, Submodule.map_comap_eq_self, Submodule.map_subtype_le, Subtype, Subtype.val_injective, fg_of_fg_map_injective, map_comap_eq_self, map_subtype_le, range_subtype, s.map, specialize, subtype, val_injective
-/
theorem isNoetherian_submodule {N : Submodule R M} :
    IsNoetherian R N ↔ forall s : Submodule R M, s <= N -> s.FG := by
  refine ⟨fun ⟨hn⟩ => fun s hs =>
    have : s <= LinearMap.range N.subtype := N.range_subtype.symm ▸ hs
    Submodule.map_comap_eq_self this ▸ (hn _).map _,
    fun h => ⟨fun s => ?_⟩⟩
  specialize h (s.map N.subtype) (Submodule.map_subtype_le N s)
  exact Submodule.fg_of_fg_map_injective N.subtype Subtype.val_injective h

/--
theorem `isNoetherian_submodule_left` / 定理 `isNoetherian_submodule_left`

English:
theorem isNoetherian_submodule_left
  given: {N : Submodule R M}
  proof: isNoetherian_submodule.trans ⟨fun H _ => H _ inf_le_left, fun H _ hs => inf_of_le_right hs ▸ H _⟩

中文:
定理 isNoetherian_submodule_left
  条件: {N : 子模 R M}
  证明: isNoetherian_submodule.trans ⟨fun H _ => H _ inf_le_left, fun H _ hs => inf_of_le_right hs ▸ H _⟩

Depends on / 依赖: inf_le_left, inf_of_le_right, isNoetherian_submodule, isNoetherian_submodule.trans
-/
theorem isNoetherian_submodule_left {N : Submodule R M} :
    IsNoetherian R N ↔ forall s : Submodule R M, (N ⊓ s).FG :=
  isNoetherian_submodule.trans ⟨fun H _ => H _ inf_le_left, fun H _ hs => inf_of_le_right hs ▸ H _⟩

/--
theorem `isNoetherian_submodule_right` / 定理 `isNoetherian_submodule_right`

English:
theorem isNoetherian_submodule_right
  given: {N : Submodule R M}
  proof: isNoetherian_submodule.trans ⟨fun H _ => H _ inf_le_right, fun H _ hs => inf_of_le_left hs ▸ H _⟩

中文:
定理 isNoetherian_submodule_right
  条件: {N : 子模 R M}
  证明: isNoetherian_submodule.trans ⟨fun H _ => H _ inf_le_right, fun H _ hs => inf_of_le_left hs ▸ H _⟩

Depends on / 依赖: inf_le_right, inf_of_le_left, isNoetherian_submodule, isNoetherian_submodule.trans
-/
theorem isNoetherian_submodule_right {N : Submodule R M} :
    IsNoetherian R N ↔ forall s : Submodule R M, (s ⊓ N).FG :=
  isNoetherian_submodule.trans ⟨fun H _ => H _ inf_le_right, fun H _ hs => inf_of_le_left hs ▸ H _⟩

/--
Instance `isNoetherian_submodule'` / 实例 `isNoetherian_submodule'`

English:
instance isNoetherian_submodule'
  signature: [IsNoetherian R M] (N : Submodule R M)
  body: isNoetherian_submodule.2 fun _ _ => IsNoetherian.noetherian _

中文:
实例 isNoetherian_submodule'
  签名: [是Noether R M] (N : 子模 R M)
  定义体: isNoetherian_submodule.2 fun _ _ => IsNoetherian.noetherian _

Depends on / 依赖: IsNoetherian, IsNoetherian.noetherian, isNoetherian_submodule, noetherian
-/
instance isNoetherian_submodule' [IsNoetherian R M] (N : Submodule R M) : IsNoetherian R N :=
  isNoetherian_submodule.2 fun _ _ => IsNoetherian.noetherian _

/--
theorem `isNoetherian_of_le` / 定理 `isNoetherian_of_le`

English:
theorem isNoetherian_of_le
  given: {s t : Submodule R M} [ht : IsNoetherian R t] (h : s <= t)
  proof: isNoetherian_submodule.mpr fun _ hs' => isNoetherian_submodule.mp ht _ (le_trans hs' h)

中文:
定理 isNoetherian_of_le
  条件: {s t : 子模 R M} [ht : 是Noether R t] (h : s <= t)
  证明: isNoetherian_submodule.mpr fun _ hs' => isNoetherian_submodule.mp ht _ (le_trans hs' h)

Depends on / 依赖: isNoetherian_submodule, isNoetherian_submodule.mp, isNoetherian_submodule.mpr, le_trans
-/
theorem isNoetherian_of_le {s t : Submodule R M} [ht : IsNoetherian R t] (h : s <= t) :
    IsNoetherian R s :=
  isNoetherian_submodule.mpr fun _ hs' => isNoetherian_submodule.mp ht _ (le_trans hs' h)

end

open IsNoetherian Submodule Function

section

universe w

variable {R M P : Type*} {N : Type w} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P]

/--
theorem `isNoetherian_iff'` / 定理 `isNoetherian_iff'`

English:
theorem isNoetherian_iff'
  statement: IsNoetherian R M ↔ WellFoundedGT (Submodule R M)
  proof: by
  refine .trans ?_ ((CompleteLattice.wellFoundedGT_characterisations <| Submodule R M).out 0 3).symm
  exact
    ⟨fun ⟨h⟩ k => (fg_iff_compact k).mp (h k), fun h =>
      ⟨fun k => (fg_iff_compact k).mpr (h k)⟩⟩

中文:
定理 isNoetherian_iff'
  结论: 是Noether R M ↔ WellFoundedGT (子模 R M)
  证明: by
  refine .trans ?_ ((CompleteLattice.wellFoundedGT_characterisations <| Submodule R M).out 0 3).symm
  exact
    ⟨fun ⟨h⟩ k => (fg_iff_compact k).mp (h k), fun h =>
      ⟨fun k => (fg_iff_compact k).mpr (h k)⟩⟩

Depends on / 依赖: CompleteLattice, CompleteLattice.wellFoundedGT_characterisations, Submodule, fg_iff_compact, wellFoundedGT_characterisations
-/
theorem isNoetherian_iff' : IsNoetherian R M ↔ WellFoundedGT (Submodule R M) := by
  refine .trans ?_ ((CompleteLattice.wellFoundedGT_characterisations <| Submodule R M).out 0 3).symm
  exact
    ⟨fun ⟨h⟩ k => (fg_iff_compact k).mp (h k), fun h =>
      ⟨fun k => (fg_iff_compact k).mpr (h k)⟩⟩

/--
theorem `isNoetherian_iff` / 定理 `isNoetherian_iff`

English:
theorem isNoetherian_iff
  proof: by
  rw [isNoetherian_iff']; rw [← isWellFounded_iff]

alias ⟨IsNoetherian.wf, _⟩ := isNoetherian_iff

alias ⟨IsNoetherian.wellFoundedGT, isNoetherian_mk⟩ := isNoetherian_iff'

中文:
定理 isNoetherian_iff
  证明: by
  rw [isNoetherian_iff']; rw [← isWellFounded_iff]

alias ⟨IsNoetherian.wf, _⟩ := isNoetherian_iff

alias ⟨IsNoetherian.wellFoundedGT, isNoetherian_mk⟩ := isNoetherian_iff'

Depends on / 依赖: isNoetherian_iff, isWellFounded_iff
-/
theorem isNoetherian_iff :
    IsNoetherian R M ↔ WellFounded ((· > ·) : Submodule R M -> Submodule R M -> Prop) := by
  rw [isNoetherian_iff']; rw [← isWellFounded_iff]

alias ⟨IsNoetherian.wf, _⟩ := isNoetherian_iff

alias ⟨IsNoetherian.wellFoundedGT, isNoetherian_mk⟩ := isNoetherian_iff'

/--
Instance `wellFoundedGT` / 实例 `wellFoundedGT`

English:
instance wellFoundedGT
  signature: [h : IsNoetherian R M]
  body: h.wellFoundedGT

中文:
实例 wellFoundedGT
  签名: [h : 是Noether R M]
  定义体: h.wellFoundedGT

Depends on / 依赖: h.wellFoundedGT, wellFoundedGT
-/
instance wellFoundedGT [h : IsNoetherian R M] : WellFoundedGT (Submodule R M) :=
  h.wellFoundedGT

/--
theorem `isNoetherian_iff_fg_wellFounded` / 定理 `isNoetherian_iff_fg_wellFounded`

English:
theorem isNoetherian_iff_fg_wellFounded
  proof: by
  let α := { N : Submodule R M // N.FG }
  constructor
  · intro H
    let f : α ↪o Submodule R M := OrderEmbedding.subtype _
    exact OrderEmbedding.wellFoundedLT f.dual
  · intro H
    constructor
    intro N
    obtain ⟨⟨N₀, h₁⟩, e : N₀ <= N, h₂⟩ :=
      WellFounded.has_min H.wf { N' : α | N

中文:
定理 isNoetherian_iff_fg_wellFounded
  证明: by
  let α := { N : Submodule R M // N.FG }
  constructor
  · intro H
    let f : α ↪o Submodule R M := OrderEmbedding.subtype _
    exact OrderEmbedding.wellFoundedLT f.dual
  · intro H
    constructor
    intro N
    obtain ⟨⟨N₀, h₁⟩, e : N₀ <= N, h₂⟩ :=
      WellFounded.has_min H.wf { N' : α | N

Depends on / 依赖: H.wf, N.FG, OrderEmbedding, OrderEmbedding.subtype, OrderEmbedding.wellFoundedLT, Set.not_subset.mp, Submodule, Submodule.fg_bot, WellFounded, WellFounded.has_min, antisymm, bot_le, convert, e.antisymm, eq_of_le_of_not_lt, f.dual, fg_bot, has_min, le_sup_right, not_subset
-/
theorem isNoetherian_iff_fg_wellFounded :
    IsNoetherian R M ↔ WellFoundedGT { N : Submodule R M // N.FG } := by
  let α := { N : Submodule R M // N.FG }
  constructor
  · intro H
    let f : α ↪o Submodule R M := OrderEmbedding.subtype _
    exact OrderEmbedding.wellFoundedLT f.dual
  · intro H
    constructor
    intro N
    obtain ⟨⟨N₀, h₁⟩, e : N₀ <= N, h₂⟩ :=
      WellFounded.has_min H.wf { N' : α | N'.1 <= N } ⟨⟨⊥, Submodule.fg_bot⟩, @bot_le _ _ _ N⟩
    convert! h₁
    refine (e.antisymm ?_).symm
    by_contra h₃
    obtain ⟨x, hx₁ : x in N, hx₂ : x ∉ N₀⟩ := Set.not_subset.mp h₃
    apply hx₂
    rw [eq_of_le_of_not_lt (le_sup_right : N₀ <= _) (h₂
⟨_]; rw [Submodule.FG.sup ⟨{x}]; rw [by rw [Finset.coe_singleton]⟩ h₁⟩
      sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) e)]
    exact (le_sup_left : R ∙ x <= _) (Submodule.mem_span_singleton_self _)

/--
theorem `set_has_maximal_iff_noetherian` / 定理 `set_has_maximal_iff_noetherian`

English:
theorem set_has_maximal_iff_noetherian
  proof: by
  rw [isNoetherian_iff]; rw [WellFounded.wellFounded_iff_has_min]

中文:
定理 set_has_maximal_iff_noetherian
  证明: by
  rw [isNoetherian_iff]; rw [WellFounded.wellFounded_iff_has_min]

Depends on / 依赖: WellFounded, WellFounded.wellFounded_iff_has_min, isNoetherian_iff, wellFounded_iff_has_min
-/
theorem set_has_maximal_iff_noetherian :
    (forall a : Set <| Submodule R M, a.Nonempty -> exists M' in a, forall I in a, ¬M' < I) ↔ IsNoetherian R M := by
  rw [isNoetherian_iff]; rw [WellFounded.wellFounded_iff_has_min]

/--
theorem `monotone_stabilizes_iff_noetherian` / 定理 `monotone_stabilizes_iff_noetherian`

English:
theorem monotone_stabilizes_iff_noetherian
  proof: by
  rw [isNoetherian_iff']; rw [wellFoundedGT_iff_monotone_chain_condition]

中文:
定理 monotone_stabilizes_iff_noetherian
  证明: by
  rw [isNoetherian_iff']; rw [wellFoundedGT_iff_monotone_chain_condition]

Depends on / 依赖: isNoetherian_iff, wellFoundedGT_iff_monotone_chain_condition
-/
theorem monotone_stabilizes_iff_noetherian :
    (forall f : Nat ->o Submodule R M, exists n, forall m, n <= m -> f n = f m) ↔ IsNoetherian R M := by
  rw [isNoetherian_iff']; rw [wellFoundedGT_iff_monotone_chain_condition]

variable [IsNoetherian R M]

open Filter
/--
theorem `Module.End.eventually_disjoint_ker_pow_range_pow` / 定理 `Module.End.eventually_disjoint_ker_pow_range_pow`

English:
theorem Module.End.eventually_disjoint_ker_pow_range_pow
  given: (f : End R M)
  proof: by
  obtain ⟨n, hn : forall m, n <= m -> LinearMap.ker (f ^ n) = LinearMap.ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine eventually_atTop.mpr ⟨n, fun m hm => disjoint_iff.mpr ?_⟩
  rw [← hn _ hm]; rw [Submodule.eq_bot_iff]
  rintro - ⟨hx, ⟨x, rfl⟩⟩
  

中文:
定理 模.End.eventually_disjoint_ker_pow_range_pow
  条件: (f : End R M)
  证明: by
  obtain ⟨n, hn : forall m, n <= m -> LinearMap.ker (f ^ n) = LinearMap.ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine eventually_atTop.mpr ⟨n, fun m hm => disjoint_iff.mpr ?_⟩
  rw [← hn _ hm]; rw [Submodule.eq_bot_iff]
  rintro - ⟨hx, ⟨x, rfl⟩⟩
  

Depends on / 依赖: LinearMap, LinearMap.ker, Submodule, Submodule.eq_bot_iff, disjoint_iff, disjoint_iff.mpr, eq_bot_iff, eventually_atTop, eventually_atTop.mpr, f.iterateKer, f.pow_apply, iterateKer, iterate_add_apply, le_add_right, monotone_stabilizes_iff_noetherian, monotone_stabilizes_iff_noetherian.mpr, n.le_add_right, pow_apply, pow_map_zero_of_le, replace
-/
theorem Module.End.eventually_disjoint_ker_pow_range_pow (f : End R M) :
    forallᶠ n in atTop, Disjoint (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn : forall m, n <= m -> LinearMap.ker (f ^ n) = LinearMap.ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine eventually_atTop.mpr ⟨n, fun m hm => disjoint_iff.mpr ?_⟩
  rw [← hn _ hm]; rw [Submodule.eq_bot_iff]
  rintro - ⟨hx, ⟨x, rfl⟩⟩
  apply pow_map_zero_of_le hm
  replace hx : x in LinearMap.ker (f ^ (n + m)) := by
    simpa [f.pow_apply n, f.pow_apply m, ← f.pow_apply (n + m), ← iterate_add_apply] using hx
  rwa [← hn _ (n.le_add_right m)] at hx

/--
lemma `LinearMap.eventually_iSup_ker_pow_eq` / 引理 `LinearMap.eventually_iSup_ker_pow_eq`

English:
lemma LinearMap.eventually_iSup_ker_pow_eq
  given: (f : M ->ₗ[R] M)
  proof: by
  obtain ⟨n, hn : forall m, n <= m -> ker (f ^ n) = ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
  refine le_antisymm (iSup_le fun l => ?_) (le_iSup (fun i => LinearMap.ker (f ^ i)) m)
  rcases le_or_gt m l

中文:
引理 线性映射.eventually_iSup_ker_pow_eq
  条件: (f : M ->ₗ[R] M)
  证明: by
  obtain ⟨n, hn : forall m, n <= m -> ker (f ^ n) = ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
  refine le_antisymm (iSup_le fun l => ?_) (le_iSup (fun i => LinearMap.ker (f ^ i)) m)
  rcases le_or_gt m l

Depends on / 依赖: LinearMap, LinearMap.ker, eventually_atTop, eventually_atTop.mpr, f.iterateKer, f.iterateKer.monotone, h.le, hm.trans, iSup_le, iterateKer, le_antisymm, le_iSup, le_or_gt, monotone, monotone_stabilizes_iff_noetherian, monotone_stabilizes_iff_noetherian.mpr
-/
lemma LinearMap.eventually_iSup_ker_pow_eq (f : M ->ₗ[R] M) :
    forallᶠ n in atTop, ⨆ m, LinearMap.ker (f ^ m) = LinearMap.ker (f ^ n) := by
  obtain ⟨n, hn : forall m, n <= m -> ker (f ^ n) = ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine eventually_atTop.mpr ⟨n, fun m hm => ?_⟩
  refine le_antisymm (iSup_le fun l => ?_) (le_iSup (fun i => LinearMap.ker (f ^ i)) m)
  rcases le_or_gt m l with h | h
  · rw [← hn _ (hm.trans h), hn _ hm]
  · exact f.iterateKer.monotone h.le

end

/-- A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated. -/
@[wikidata Q582271]
/--
Definition of `IsNoetherianRing` / `IsNoetherianRing` 的定义

English:
abbreviation IsNoetherianRing
  signature: (R) [Semiring R]
  body: IsNoetherian R R

中文:
缩写 是Noether环
  签名: (R) [半环 R]
  定义体: IsNoetherian R R

Depends on / 依赖: IsNoetherian
-/
abbrev IsNoetherianRing (R) [Semiring R] :=
  IsNoetherian R R

/--
theorem `isNoetherianRing_iff` / 定理 `isNoetherianRing_iff`

English:
theorem isNoetherianRing_iff
  given: {R} [Semiring R]
  statement: IsNoetherianRing R ↔ IsNoetherian R R
  proof: Iff.rfl

中文:
定理 isNoetherianRing_iff
  条件: {R} [半环 R]
  结论: 是Noether环 R ↔ 是Noether R R
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isNoetherianRing_iff {R} [Semiring R] : IsNoetherianRing R ↔ IsNoetherian R R :=
  Iff.rfl

/--
theorem `isNoetherianRing_iff_ideal_fg` / 定理 `isNoetherianRing_iff_ideal_fg`

English:
theorem isNoetherianRing_iff_ideal_fg
  given: (R : Type*) [Semiring R]
  proof: isNoetherianRing_iff.trans isNoetherian_def

中文:
定理 isNoetherianRing_iff_ideal_fg
  条件: (R : 类型) [半环 R]
  证明: isNoetherianRing_iff.trans isNoetherian_def

Depends on / 依赖: isNoetherianRing_iff, isNoetherianRing_iff.trans, isNoetherian_def
-/
theorem isNoetherianRing_iff_ideal_fg (R : Type*) [Semiring R] :
    IsNoetherianRing R ↔ forall I : Ideal R, I.FG :=
  isNoetherianRing_iff.trans isNoetherian_def

/--
lemma `Ideal.fg_of_isNoetherianRing` / 引理 `Ideal.fg_of_isNoetherianRing`

English:
lemma Ideal.fg_of_isNoetherianRing
  given: {R : Type*} [Semiring R] [IsNoetherianRing R] (I : Ideal R)
  proof: IsNoetherian.noetherian _

alias Ideal.FG.of_isNoetherianRing := Ideal.fg_of_isNoetherianRing

中文:
引理 理想.fg_of_isNoetherianRing
  条件: {R : 类型} [半环 R] [是Noether环 R] (I : 理想 R)
  证明: IsNoetherian.noetherian _

alias Ideal.FG.of_isNoetherianRing := Ideal.fg_of_isNoetherianRing

Depends on / 依赖: IsNoetherian, IsNoetherian.noetherian, noetherian
-/
lemma Ideal.fg_of_isNoetherianRing {R : Type*} [Semiring R] [IsNoetherianRing R] (I : Ideal R) :
    I.FG :=
  IsNoetherian.noetherian _

alias Ideal.FG.of_isNoetherianRing := Ideal.fg_of_isNoetherianRing
