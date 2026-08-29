/-
Copyright (c) 2020 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Torsion

/-!
# Basic results on subgroups

We prove basic results on the definitions of subgroups. The bundled subgroups use bundled monoid
homomorphisms.

Special thanks goes to Amelia Livingston and Yury Kudryashov for their help and inspiration.

## Main definitions

Notation used here:

- `G N` are `Group`s

- `A` is an `AddGroup`

- `H K` are `Subgroup`s of `G` or `AddSubgroup`s of `A`

- `x` is an element of type `G` or type `A`

- `f g : N →* G` are group homomorphisms

- `s k` are sets of elements of type `G`

Definitions in the file:

* `Subgroup.prod H K` : the product of subgroups `H`, `K` of groups `G`, `N` respectively, `H × K`
  is a subgroup of `G × N`

## Implementation notes

Subgroup inclusion is denoted `≤` rather than `⊆`, although `∈` is defined as
membership of a subgroup's underlying set.

## Tags
subgroup, subgroups
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Multiset Ring

open Function
open scoped Int

variable {G G' G'' : Type*} [Group G] [Group G'] [Group G'']
variable {A : Type*} [AddGroup A]

section SubgroupClass

variable {M S : Type*} [DivInvMonoid M] [SetLike S M] [hSM : SubgroupClass S M] {H K : S}

variable [SetLike S G] [SubgroupClass S G]

@[to_additive]
/--
theorem `div_mem_comm_iff` / 定理 `div_mem_comm_iff`

English:
theorem div_mem_comm_iff
  given: {a b : G}
  statement: a / b in H ↔ b / a in H
  proof: inv_div b a ▸ inv_mem_iff

中文:
定理 div_mem_comm_iff
  条件: {a b : G}
  结论: a / b in H ↔ b / a in H
  证明: inv_div b a ▸ inv_mem_iff

Depends on / 依赖: inv_div, inv_mem_iff
-/
theorem div_mem_comm_iff {a b : G} : a / b in H ↔ b / a in H :=
  inv_div b a ▸ inv_mem_iff

end SubgroupClass

namespace Subgroup

variable (H K : Subgroup G)

@[to_additive]
/--
theorem `div_mem_comm_iff` / 定理 `div_mem_comm_iff`

English:
theorem div_mem_comm_iff
  given: {a b : G}
  statement: a / b in H ↔ b / a in H
  proof: div_mem_comm_iff

中文:
定理 div_mem_comm_iff
  条件: {a b : G}
  结论: a / b in H ↔ b / a in H
  证明: div_mem_comm_iff
-/
protected theorem div_mem_comm_iff {a b : G} : a / b in H ↔ b / a in H :=
  div_mem_comm_iff

variable {k : Set G}

open Set

variable {N : Type*} [Group N] {P : Type*} [Group P]

/-- Given `Subgroup`s `H`, `K` of groups `G`, `N` respectively, `H × K` as a subgroup of `G × N`. -/
@[to_additive prod
      /-- Given `AddSubgroup`s `H`, `K` of `AddGroup`s `A`, `B` respectively, `H × K`
      as an `AddSubgroup` of `A × B`. -/]
/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: (H : Subgroup G) (K : Subgroup N)
  body: { Submonoid.prod H.toSubmonoid K.toSubmonoid with
    inv_mem' := fun hx => ⟨H.inv_mem' hx.1, K.inv_mem' hx.2⟩ }

@[to_additive (attr := norm_cast) coe_prod]

中文:
定义 prod
  签名: (H : Subgroup G) (K : Subgroup N)
  定义体: { Submonoid.prod H.toSubmonoid K.toSubmonoid with
    inv_mem' := fun hx => ⟨H.inv_mem' hx.1, K.inv_mem' hx.2⟩ }

@[to_additive (attr := norm_cast) coe_prod]

Depends on / 依赖: H.inv_mem, H.toSubmonoid, K.inv_mem, K.toSubmonoid, Submonoid, Submonoid.prod, inv_mem, toSubmonoid
-/
def prod (H : Subgroup G) (K : Subgroup N) : Subgroup (G × N) :=
  { Submonoid.prod H.toSubmonoid K.toSubmonoid with
    inv_mem' := fun hx => ⟨H.inv_mem' hx.1, K.inv_mem' hx.2⟩ }

@[to_additive (attr := norm_cast) coe_prod]
/--
theorem `coe_prod` / 定理 `coe_prod`

English:
theorem coe_prod
  given: (H : Subgroup G) (K : Subgroup N)
  proof: rfl

@[to_additive mem_prod]

中文:
定理 coe_prod
  条件: (H : Subgroup G) (K : Subgroup N)
  证明: rfl

@[to_additive mem_prod]
-/
theorem coe_prod (H : Subgroup G) (K : Subgroup N) :
    (H.prod K : Set (G × N)) = (H : Set G) ×ˢ (K : Set N) :=
  rfl

@[to_additive mem_prod]
/--
theorem `mem_prod` / 定理 `mem_prod`

English:
theorem mem_prod
  given: {H : Subgroup G} {K : Subgroup N} {p : G × N}
  statement: p in H.prod K ↔ p.1 in H ∧ p.2 in K
  proof: Iff.rfl

中文:
定理 mem_prod
  条件: {H : Subgroup G} {K : Subgroup N} {p : G × N}
  结论: p in H.prod K ↔ p.1 in H ∧ p.2 in K
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_prod {H : Subgroup G} {K : Subgroup N} {p : G × N} : p in H.prod K ↔ p.1 in H ∧ p.2 in K :=
  Iff.rfl

open scoped Relator in
@[to_additive prod_mono]
/--
theorem `prod_mono` / 定理 `prod_mono`

English:
theorem prod_mono
  statement: ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) (@prod G _ N _) (@prod G _ N _)
  proof: fun _s _s' hs _t _t' ht => Set.prod_mono hs ht

@[to_additive prod_mono_right]

中文:
定理 prod_mono
  结论: ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) (@prod G _ N _) (@prod G _ N _)
  证明: fun _s _s' hs _t _t' ht => Set.prod_mono hs ht

@[to_additive prod_mono_right]

Depends on / 依赖: Set.prod_mono, Set.rangeFactorization_surjective.countable, countable, prod_mono, rangeFactorization_surjective
-/
theorem prod_mono : ((· <= ·) ⇒ (· <= ·) ⇒ (· <= ·)) (@prod G _ N _) (@prod G _ N _) :=
  fun _s _s' hs _t _t' ht => Set.prod_mono hs ht

@[to_additive prod_mono_right]
/--
theorem `prod_mono_right` / 定理 `prod_mono_right`

English:
theorem prod_mono_right
  given: (K : Subgroup G)
  statement: Monotone fun t : Subgroup N => K.prod t
  proof: prod_mono (le_refl K)

@[to_additive prod_mono_left]

中文:
定理 prod_mono_right
  条件: (K : Subgroup G)
  结论: Monotone fun t : Subgroup N => K.prod t
  证明: prod_mono (le_refl K)

@[to_additive prod_mono_left]

Depends on / 依赖: le_refl, prod_mono
-/
theorem prod_mono_right (K : Subgroup G) : Monotone fun t : Subgroup N => K.prod t :=
  prod_mono (le_refl K)

@[to_additive prod_mono_left]
/--
theorem `prod_mono_left` / 定理 `prod_mono_left`

English:
theorem prod_mono_left
  given: (H : Subgroup N)
  statement: Monotone fun K : Subgroup G => K.prod H
  proof: fun _ _ hs =>
  prod_mono hs (le_refl H)

@[to_additive prod_top]

中文:
定理 prod_mono_left
  条件: (H : Subgroup N)
  结论: Monotone fun K : Subgroup G => K.prod H
  证明: fun _ _ hs =>
  prod_mono hs (le_refl H)

@[to_additive prod_top]
-/
theorem prod_mono_left (H : Subgroup N) : Monotone fun K : Subgroup G => K.prod H := fun _ _ hs =>
  prod_mono hs (le_refl H)

@[to_additive prod_top]
/--
theorem `prod_top` / 定理 `prod_top`

English:
theorem prod_top
  given: (K : Subgroup G)
  statement: K.prod (⊤ : Subgroup N) = K.comap (MonoidHom.fst G N)
  proof: ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

@[to_additive top_prod]

中文:
定理 prod_top
  条件: (K : Subgroup G)
  结论: K.prod (⊤ : Subgroup N) = K.comap (MonoidHom.fst G N)
  证明: ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

@[to_additive top_prod]

Depends on / 依赖: MonoidHom, MonoidHom.coe_fst, coe_fst, mem_prod
-/
theorem prod_top (K : Subgroup G) : K.prod (⊤ : Subgroup N) = K.comap (MonoidHom.fst G N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_fst]

@[to_additive top_prod]
/--
theorem `top_prod` / 定理 `top_prod`

English:
theorem top_prod
  given: (H : Subgroup N)
  statement: (⊤ : Subgroup G).prod H = H.comap (MonoidHom.snd G N)
  proof: ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]

中文:
定理 top_prod
  条件: (H : Subgroup N)
  结论: (⊤ : Subgroup G).prod H = H.comap (MonoidHom.snd G N)
  证明: ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]

Depends on / 依赖: MonoidHom, MonoidHom.coe_snd, coe_snd, mem_prod
-/
theorem top_prod (H : Subgroup N) : (⊤ : Subgroup G).prod H = H.comap (MonoidHom.snd G N) :=
  ext fun x => by simp [mem_prod, MonoidHom.coe_snd]

@[to_additive (attr := simp) top_prod_top]
/--
theorem `top_prod_top` / 定理 `top_prod_top`

English:
theorem top_prod_top
  statement: (⊤ : Subgroup G).prod (⊤ : Subgroup N) = ⊤
  proof: (top_prod _).trans comap_top _

@[to_additive (attr := simp) bot_prod_bot]

中文:
定理 top_prod_top
  结论: (⊤ : Subgroup G).prod (⊤ : Subgroup N) = ⊤
  证明: (top_prod _).trans comap_top _

@[to_additive (attr := simp) bot_prod_bot]

Depends on / 依赖: comap_top, top_prod
-/
theorem top_prod_top : (⊤ : Subgroup G).prod (⊤ : Subgroup N) = ⊤ :=
(top_prod _).trans comap_top _

@[to_additive (attr := simp) bot_prod_bot]
/--
theorem `bot_prod_bot` / 定理 `bot_prod_bot`

English:
theorem bot_prod_bot
  statement: (⊥ : Subgroup G).prod (⊥ : Subgroup N) = ⊥
  proof: SetLike.coe_injective by simp [coe_prod]

@[to_additive le_prod_iff]

中文:
定理 bot_prod_bot
  结论: (⊥ : Subgroup G).prod (⊥ : Subgroup N) = ⊥
  证明: SetLike.coe_injective by simp [coe_prod]

@[to_additive le_prod_iff]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, coe_prod
-/
theorem bot_prod_bot : (⊥ : Subgroup G).prod (⊥ : Subgroup N) = ⊥ :=
SetLike.coe_injective by simp [coe_prod]

@[to_additive le_prod_iff]
/--
theorem `le_prod_iff` / 定理 `le_prod_iff`

English:
theorem le_prod_iff
  given: {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)}
  proof: by
  simpa only [← Subgroup.toSubmonoid_le] using! Submonoid.le_prod_iff

@[to_additive prod_le_iff]

中文:
定理 le_prod_iff
  条件: {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)}
  证明: by
  simpa only [← Subgroup.toSubmonoid_le] using! Submonoid.le_prod_iff

@[to_additive prod_le_iff]

Depends on / 依赖: Subgroup, Subgroup.toSubmonoid_le, Submonoid, Submonoid.le_prod_iff, le_prod_iff, toSubmonoid_le
-/
theorem le_prod_iff {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)} :
    J <= H.prod K ↔ map (MonoidHom.fst G N) J <= H ∧ map (MonoidHom.snd G N) J <= K := by
  simpa only [← Subgroup.toSubmonoid_le] using! Submonoid.le_prod_iff

@[to_additive prod_le_iff]
/--
theorem `prod_le_iff` / 定理 `prod_le_iff`

English:
theorem prod_le_iff
  given: {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)}
  proof: by
  simpa only [← Subgroup.toSubmonoid_le] using! Submonoid.prod_le_iff

@[to_additive (attr := simp) prod_eq_bot_iff]

中文:
定理 prod_le_iff
  条件: {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)}
  证明: by
  simpa only [← Subgroup.toSubmonoid_le] using! Submonoid.prod_le_iff

@[to_additive (attr := simp) prod_eq_bot_iff]

Depends on / 依赖: Subgroup, Subgroup.toSubmonoid_le, Submonoid, Submonoid.prod_le_iff, prod_le_iff, toSubmonoid_le
-/
theorem prod_le_iff {H : Subgroup G} {K : Subgroup N} {J : Subgroup (G × N)} :
    H.prod K <= J ↔ map (MonoidHom.inl G N) H <= J ∧ map (MonoidHom.inr G N) K <= J := by
  simpa only [← Subgroup.toSubmonoid_le] using! Submonoid.prod_le_iff

@[to_additive (attr := simp) prod_eq_bot_iff]
/--
theorem `prod_eq_bot_iff` / 定理 `prod_eq_bot_iff`

English:
theorem prod_eq_bot_iff
  given: {H : Subgroup G} {K : Subgroup N}
  statement: H.prod K = ⊥ ↔ H = ⊥ ∧ K = ⊥
  proof: by
  simpa only [← Subgroup.toSubmonoid_inj] using! Submonoid.prod_eq_bot_iff

@[to_additive closure_prod]

中文:
定理 prod_eq_bot_iff
  条件: {H : Subgroup G} {K : Subgroup N}
  结论: H.prod K = ⊥ ↔ H = ⊥ ∧ K = ⊥
  证明: by
  simpa only [← Subgroup.toSubmonoid_inj] using! Submonoid.prod_eq_bot_iff

@[to_additive closure_prod]

Depends on / 依赖: Subgroup, Subgroup.toSubmonoid_inj, Submonoid, Submonoid.prod_eq_bot_iff, prod_eq_bot_iff, toSubmonoid_inj
-/
theorem prod_eq_bot_iff {H : Subgroup G} {K : Subgroup N} : H.prod K = ⊥ ↔ H = ⊥ ∧ K = ⊥ := by
  simpa only [← Subgroup.toSubmonoid_inj] using! Submonoid.prod_eq_bot_iff

@[to_additive closure_prod]
/--
theorem `closure_prod` / 定理 `closure_prod`

English:
theorem closure_prod
  given: {s : Set G} {t : Set N} (hs : 1 in s) (ht : 1 in t)
  proof: le_antisymm
    (closure_le _ |>.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, subset_closure⟩)
    (prod_le_iff.2 ⟨
map_le_iff_le_comap.2 .2 fun _x hx => subset_closure ⟨hx, ht⟩, closure_le _
map_le_iff_le_comap.2 .2 fun _y hy => subset_closure ⟨hs, hy⟩⟩) closure_le _

中文:
定理 closure_prod
  条件: {s : Set G} {t : Set N} (hs : 1 in s) (ht : 1 in t)
  证明: le_antisymm
    (closure_le _ |>.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, subset_closure⟩)
    (prod_le_iff.2 ⟨
map_le_iff_le_comap.2 .2 fun _x hx => subset_closure ⟨hx, ht⟩, closure_le _
map_le_iff_le_comap.2 .2 fun _y hy => subset_closure ⟨hs, hy⟩⟩) closure_le _

Depends on / 依赖: Set.prod_subset_prod_iff, closure_le, le_antisymm, map_le_iff_le_comap, prod_le_iff, prod_subset_prod_iff, subset_closure
-/
theorem closure_prod {s : Set G} {t : Set N} (hs : 1 in s) (ht : 1 in t) :
    closure (s ×ˢ t) = (closure s).prod (closure t) :=
  le_antisymm
    (closure_le _ |>.2 <| Set.prod_subset_prod_iff.2 <| .inl ⟨subset_closure, subset_closure⟩)
    (prod_le_iff.2 ⟨
map_le_iff_le_comap.2 .2 fun _x hx => subset_closure ⟨hx, ht⟩, closure_le _
map_le_iff_le_comap.2 .2 fun _y hy => subset_closure ⟨hs, hy⟩⟩) closure_le _

/-- Product of subgroups is isomorphic to their product as groups. -/
@[to_additive prodEquiv
      /-- Product of additive subgroups is isomorphic to their product
      as additive groups -/]
/--
Definition of `prodEquiv` / `prodEquiv` 的定义

English:
definition prodEquiv
  signature: (H : Subgroup G) (K : Subgroup N)
  body: { Equiv.Set.prod (H : Set G) (K : Set N) with map_mul' := fun _ _ => rfl }

中文:
定义 prodEquiv
  签名: (H : Subgroup G) (K : Subgroup N)
  定义体: { Equiv.Set.prod (H : Set G) (K : Set N) with map_mul' := fun _ _ => rfl }

Depends on / 依赖: Equiv.Set.prod, map_mul
-/
def prodEquiv (H : Subgroup G) (K : Subgroup N) : H.prod K ≃* H × K :=
  { Equiv.Set.prod (H : Set G) (K : Set N) with map_mul' := fun _ _ => rfl }

section Pi

variable {η : Type*} {f : η -> Type*}

variable [forall i, Group (f i)]

/-- A version of `Set.pi` for subgroups. Given an index set `I` and a family of submodules
`s : Π i, Subgroup f i`, `pi I s` is the subgroup of dependent functions `f : Π i, f i` such that
`f i` belongs to `pi I s` whenever `i ∈ I`. -/
@[to_additive
      /-- A version of `Set.pi` for `AddSubgroup`s. Given an index set `I` and a family
      of submodules `s : Π i, AddSubgroup f i`, `pi I s` is the `AddSubgroup` of dependent functions
      `f : Π i, f i` such that `f i` belongs to `pi I s` whenever `i ∈ I`. -/]
/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (I : Set η) (H : forall i, Subgroup (f i))
  body: { Submonoid.pi I fun i => (H i).toSubmonoid with
    inv_mem' := fun hp i hI => (H i).inv_mem (hp i hI) }

@[to_additive]

中文:
定义 pi
  签名: (I : Set η) (H : 对任意 i, Subgroup (f i))
  定义体: { Submonoid.pi I fun i => (H i).toSubmonoid with
    inv_mem' := fun hp i hI => (H i).inv_mem (hp i hI) }

@[to_additive]

Depends on / 依赖: Submonoid, Submonoid.pi, inv_mem, toSubmonoid
-/
def pi (I : Set η) (H : forall i, Subgroup (f i)) : Subgroup (forall i, f i) :=
  { Submonoid.pi I fun i => (H i).toSubmonoid with
    inv_mem' := fun hp i hI => (H i).inv_mem (hp i hI) }

@[to_additive]
/--
theorem `coe_pi` / 定理 `coe_pi`

English:
theorem coe_pi
  given: (I : Set η) (H : forall i, Subgroup (f i))
  proof: rfl

@[to_additive]

中文:
定理 coe_pi
  条件: (I : Set η) (H : 对任意 i, Subgroup (f i))
  证明: rfl

@[to_additive]
-/
theorem coe_pi (I : Set η) (H : forall i, Subgroup (f i)) :
    (pi I H : Set (forall i, f i)) = Set.pi I fun i => (H i : Set (f i)) :=
  rfl

@[to_additive]
/--
theorem `mem_pi` / 定理 `mem_pi`

English:
theorem mem_pi
  given: (I : Set η) {H : forall i, Subgroup (f i)} {p : forall i, f i}
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_pi
  条件: (I : Set η) {H : 对任意 i, Subgroup (f i)} {p : 对任意 i, f i}
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_pi (I : Set η) {H : forall i, Subgroup (f i)} {p : forall i, f i} :
    p in pi I H ↔ forall i : η, i in I -> p i in H i :=
  Iff.rfl

@[to_additive]
/--
theorem `pi_top` / 定理 `pi_top`

English:
theorem pi_top
  given: (I : Set η)
  statement: (pi I fun i => (⊤ : Subgroup (f i))) = ⊤
  proof: ext fun x => by simp [mem_pi]

@[to_additive]

中文:
定理 pi_top
  条件: (I : Set η)
  结论: (pi I fun i => (⊤ : Subgroup (f i))) = ⊤
  证明: ext fun x => by simp [mem_pi]

@[to_additive]

Depends on / 依赖: mem_pi
-/
theorem pi_top (I : Set η) : (pi I fun i => (⊤ : Subgroup (f i))) = ⊤ :=
  ext fun x => by simp [mem_pi]

@[to_additive]
/--
theorem `pi_empty` / 定理 `pi_empty`

English:
theorem pi_empty
  given: (H : forall i, Subgroup (f i))
  statement: pi ∅ H = ⊤
  proof: ext fun x => by simp [mem_pi]

@[to_additive]

中文:
定理 pi_empty
  条件: (H : 对任意 i, Subgroup (f i))
  结论: pi ∅ H = ⊤
  证明: ext fun x => by simp [mem_pi]

@[to_additive]

Depends on / 依赖: mem_pi
-/
theorem pi_empty (H : forall i, Subgroup (f i)) : pi ∅ H = ⊤ :=
  ext fun x => by simp [mem_pi]

@[to_additive]
/--
theorem `pi_bot` / 定理 `pi_bot`

English:
theorem pi_bot
  statement: (pi Set.univ fun i => (⊥ : Subgroup (f i))) = ⊥
  proof: ext fun x => by simp [mem_pi, funext_iff]

@[to_additive]

中文:
定理 pi_bot
  结论: (pi Set.univ fun i => (⊥ : Subgroup (f i))) = ⊥
  证明: ext fun x => by simp [mem_pi, funext_iff]

@[to_additive]

Depends on / 依赖: funext_iff, mem_pi
-/
theorem pi_bot : (pi Set.univ fun i => (⊥ : Subgroup (f i))) = ⊥ :=
  ext fun x => by simp [mem_pi, funext_iff]

@[to_additive]
/--
theorem `le_pi_iff` / 定理 `le_pi_iff`

English:
theorem le_pi_iff
  given: {I : Set η} {H : forall i, Subgroup (f i)} {J : Subgroup (forall i, f i)}
  proof: Set.subset_pi_iff

@[to_additive (attr := simp)]

中文:
定理 le_pi_iff
  条件: {I : Set η} {H : 对任意 i, Subgroup (f i)} {J : Subgroup (对任意 i, f i)}
  证明: Set.subset_pi_iff

@[to_additive (attr := simp)]

Depends on / 依赖: Set.subset_pi_iff, subset_pi_iff
-/
theorem le_pi_iff {I : Set η} {H : forall i, Subgroup (f i)} {J : Subgroup (forall i, f i)} :
    J <= pi I H ↔ forall i in I, J <= comap (Pi.evalMonoidHom f i) (H i) :=
  Set.subset_pi_iff

@[to_additive (attr := simp)]
/--
theorem `mulSingle_mem_pi` / 定理 `mulSingle_mem_pi`

English:
theorem mulSingle_mem_pi
  given: [DecidableEq η] {I : Set η} {H : forall i, Subgroup (f i)} (i : η) (x : f i)
  proof: Set.update_mem_pi_iff_of_mem (one_mem (pi I H))

@[to_additive]

中文:
定理 mulSingle_mem_pi
  条件: [DecidableEq η] {I : Set η} {H : 对任意 i, Subgroup (f i)} (i : η) (x : f i)
  证明: Set.update_mem_pi_iff_of_mem (one_mem (pi I H))

@[to_additive]

Depends on / 依赖: Set.update_mem_pi_iff_of_mem, one_mem, update_mem_pi_iff_of_mem
-/
theorem mulSingle_mem_pi [DecidableEq η] {I : Set η} {H : forall i, Subgroup (f i)} (i : η) (x : f i) :
    Pi.mulSingle i x in pi I H ↔ i in I -> x in H i :=
  Set.update_mem_pi_iff_of_mem (one_mem (pi I H))

@[to_additive]
/--
theorem `pi_eq_bot_iff` / 定理 `pi_eq_bot_iff`

English:
theorem pi_eq_bot_iff
  given: (H : forall i, Subgroup (f i))
  statement: pi Set.univ H = ⊥ ↔ forall i, H i = ⊥
  proof: by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

中文:
定理 pi_eq_bot_iff
  条件: (H : 对任意 i, Subgroup (f i))
  结论: pi Set.univ H = ⊥ ↔ 对任意 i, H i = ⊥
  证明: by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

Depends on / 依赖: Set.univ_pi_eq_singleton_iff, SetLike, SetLike.ext, _iff, simp_rw, univ_pi_eq_singleton_iff
-/
theorem pi_eq_bot_iff (H : forall i, Subgroup (f i)) : pi Set.univ H = ⊥ ↔ forall i, H i = ⊥ := by
  simp_rw [SetLike.ext'_iff]
  exact Set.univ_pi_eq_singleton_iff

end Pi

@[to_additive]
/--
Instance `instIsMulTorsionFree` / 实例 `instIsMulTorsionFree`

English:
instance instIsMulTorsionFree
  signature: [IsMulTorsionFree G]
  body: by
    have := pow_left_injective hn (M := G) (a₁ := a) (a₂ := b)
    dsimp at *
    norm_cast at this

中文:
实例 instIsMulTorsionFree
  签名: [IsMulTorsionFree G]
  定义体: by
    have := pow_left_injective hn (M := G) (a₁ := a) (a₂ := b)
    dsimp at *
    norm_cast at this

Depends on / 依赖: pow_left_injective
-/
instance instIsMulTorsionFree [IsMulTorsionFree G] : IsMulTorsionFree H where
  pow_left_injective n hn a b := by
    have := pow_left_injective hn (M := G) (a₁ := a) (a₂ := b)
    dsimp at *
    norm_cast at this

end Subgroup

namespace Subgroup

variable {H K : Subgroup G}

variable (H)

/--
Definition of `Characteristic` / `Characteristic` 的定义

English:
structure Characteristic
  parameters: : Prop where
  axioms and operations (1):
    - fixed : forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H

中文:
结构 Characteristic
  参数: : 命题 where
  公理与运算 (1 个):
    - fixed : 对任意 ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H
-/
structure Characteristic : Prop where
  /-- `H` is fixed by all automorphisms -/
  fixed : forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H

attribute [class] Characteristic

instance (priority := 100) normal_of_characteristic [h : H.Characteristic] : H.Normal :=
  ⟨fun a ha b => (SetLike.ext_iff.mp (h.fixed (MulAut.conj b)) a).mpr ha⟩

end Subgroup

namespace AddSubgroup

variable (H : AddSubgroup A)

/--
Definition of `Characteristic` / `Characteristic` 的定义

English:
structure Characteristic
  parameters: : Prop where
  axioms and operations (1):
    - fixed : forall ϕ : A ≃+ A, H.comap ϕ.toAddMonoidHom = H

中文:
结构 Characteristic
  参数: : 命题 where
  公理与运算 (1 个):
    - fixed : 对任意 ϕ : A ≃+ A, H.comap ϕ.toAddMonoidHom = H
-/
structure Characteristic : Prop where
  /-- `H` is fixed by all automorphisms -/
  fixed : forall ϕ : A ≃+ A, H.comap ϕ.toAddMonoidHom = H

attribute [to_additive] Subgroup.Characteristic

attribute [class] Characteristic

instance (priority := 100) normal_of_characteristic [h : H.Characteristic] : H.Normal :=
  ⟨fun a ha b => (SetLike.ext_iff.mp (h.fixed (AddAut.addConj b)) a).mpr ha⟩

end AddSubgroup

namespace Subgroup

/-- The whole group `G` is normal. -/
@[to_additive (attr := simp) /-- The whole group `G` is normal. -/]
/--
Instance `normal_top` / 实例 `normal_top`

English:
instance normal_top
  signature: : (⊤ : Subgroup G).Normal where
  body: a

中文:
实例 normal_top
  签名: : (⊤ : Subgroup G).Normal where
  定义体: a
-/
instance normal_top : (⊤ : Subgroup G).Normal where
  conj_mem _ a _ := a

/-- The trivial subgroup `{1}` is normal. -/
@[to_additive (attr := simp) /-- The trivial subgroup `{0}` is normal. -/]
/--
Instance `normal_bot` / 实例 `normal_bot`

English:
instance normal_bot
  signature: : (⊥ : Subgroup G).Normal where
  body: by simp

中文:
实例 normal_bot
  签名: : (⊥ : Subgroup G).Normal where
  定义体: by simp
-/
instance normal_bot : (⊥ : Subgroup G).Normal where
  conj_mem := by simp

variable {H K : Subgroup G}

@[to_additive]
/--
theorem `characteristic_iff_comap_eq` / 定理 `characteristic_iff_comap_eq`

English:
theorem characteristic_iff_comap_eq
  statement: H.Characteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H
  proof: ⟨Characteristic.fixed, Characteristic.mk⟩

@[to_additive]

中文:
定理 characteristic_iff_comap_eq
  结论: H.Characteristic ↔ 对任意 ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H
  证明: ⟨Characteristic.fixed, Characteristic.mk⟩

@[to_additive]

Depends on / 依赖: Characteristic, Characteristic.fixed, Characteristic.mk
-/
theorem characteristic_iff_comap_eq : H.Characteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom = H :=
  ⟨Characteristic.fixed, Characteristic.mk⟩

@[to_additive]
/--
theorem `characteristic_iff_comap_le` / 定理 `characteristic_iff_comap_le`

English:
theorem characteristic_iff_comap_le
  statement: H.Characteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom <= H
  proof: characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => le_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (h ϕ) fun g hg => h ϕ.symm ((congr_arg (· in H) (ϕ.symm_apply_apply g)).mpr hg)⟩

@[to_additive]

中文:
定理 characteristic_iff_comap_le
  结论: H.Characteristic ↔ 对任意 ϕ : G ≃* G, H.comap ϕ.toMonoidHom <= H
  证明: characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => le_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (h ϕ) fun g hg => h ϕ.symm ((congr_arg (· in H) (ϕ.symm_apply_apply g)).mpr hg)⟩

@[to_additive]

Depends on / 依赖: characteristic_iff_comap_eq, characteristic_iff_comap_eq.trans, congr_arg, le_antisymm, le_of_eq, symm_apply_apply
-/
theorem characteristic_iff_comap_le : H.Characteristic ↔ forall ϕ : G ≃* G, H.comap ϕ.toMonoidHom <= H :=
  characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => le_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (h ϕ) fun g hg => h ϕ.symm ((congr_arg (· in H) (ϕ.symm_apply_apply g)).mpr hg)⟩

@[to_additive]
/--
theorem `characteristic_iff_le_comap` / 定理 `characteristic_iff_le_comap`

English:
theorem characteristic_iff_le_comap
  statement: H.Characteristic ↔ forall ϕ : G ≃* G, H <= H.comap ϕ.toMonoidHom
  proof: characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => ge_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (fun g hg => (congr_arg (· in H) (ϕ.symm_apply_apply g)).mp (h ϕ.symm hg)) (h ϕ)⟩

@[to_additive]

中文:
定理 characteristic_iff_le_comap
  结论: H.Characteristic ↔ 对任意 ϕ : G ≃* G, H <= H.comap ϕ.toMonoidHom
  证明: characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => ge_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (fun g hg => (congr_arg (· in H) (ϕ.symm_apply_apply g)).mp (h ϕ.symm hg)) (h ϕ)⟩

@[to_additive]

Depends on / 依赖: characteristic_iff_comap_eq, characteristic_iff_comap_eq.trans, congr_arg, ge_of_eq, le_antisymm, symm_apply_apply
-/
theorem characteristic_iff_le_comap : H.Characteristic ↔ forall ϕ : G ≃* G, H <= H.comap ϕ.toMonoidHom :=
  characteristic_iff_comap_eq.trans
    ⟨fun h ϕ => ge_of_eq (h ϕ), fun h ϕ =>
      le_antisymm (fun g hg => (congr_arg (· in H) (ϕ.symm_apply_apply g)).mp (h ϕ.symm hg)) (h ϕ)⟩

@[to_additive]
/--
theorem `characteristic_iff_map_eq` / 定理 `characteristic_iff_map_eq`

English:
theorem characteristic_iff_map_eq
  statement: H.Characteristic ↔ forall ϕ : G ≃* G, H.map ϕ.toMonoidHom = H
  proof: by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_comap_eq.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]

中文:
定理 characteristic_iff_map_eq
  结论: H.Characteristic ↔ 对任意 ϕ : G ≃* G, H.map ϕ.toMonoidHom = H
  证明: by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_comap_eq.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]

Depends on / 依赖: characteristic_iff_comap_eq, characteristic_iff_comap_eq.trans, map_equiv_eq_comap_symm, simp_rw
-/
theorem characteristic_iff_map_eq : H.Characteristic ↔ forall ϕ : G ≃* G, H.map ϕ.toMonoidHom = H := by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_comap_eq.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]
/--
theorem `characteristic_iff_map_le` / 定理 `characteristic_iff_map_le`

English:
theorem characteristic_iff_map_le
  statement: H.Characteristic ↔ forall ϕ : G ≃* G, H.map ϕ.toMonoidHom <= H
  proof: by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_comap_le.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]

中文:
定理 characteristic_iff_map_le
  结论: H.Characteristic ↔ 对任意 ϕ : G ≃* G, H.map ϕ.toMonoidHom <= H
  证明: by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_comap_le.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]

Depends on / 依赖: characteristic_iff_comap_le, characteristic_iff_comap_le.trans, map_equiv_eq_comap_symm, simp_rw
-/
theorem characteristic_iff_map_le : H.Characteristic ↔ forall ϕ : G ≃* G, H.map ϕ.toMonoidHom <= H := by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_comap_le.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]
/--
theorem `characteristic_iff_le_map` / 定理 `characteristic_iff_le_map`

English:
theorem characteristic_iff_le_map
  statement: H.Characteristic ↔ forall ϕ : G ≃* G, H <= H.map ϕ.toMonoidHom
  proof: by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_le_comap.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]

中文:
定理 characteristic_iff_le_map
  结论: H.Characteristic ↔ 对任意 ϕ : G ≃* G, H <= H.map ϕ.toMonoidHom
  证明: by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_le_comap.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]

Depends on / 依赖: characteristic_iff_le_comap, characteristic_iff_le_comap.trans, map_equiv_eq_comap_symm, simp_rw
-/
theorem characteristic_iff_le_map : H.Characteristic ↔ forall ϕ : G ≃* G, H <= H.map ϕ.toMonoidHom := by
  simp_rw [map_equiv_eq_comap_symm']
  exact characteristic_iff_le_comap.trans ⟨fun h ϕ => h ϕ.symm, fun h ϕ => h ϕ.symm⟩

@[to_additive]
/--
Instance `botCharacteristic` / 实例 `botCharacteristic`

English:
instance botCharacteristic
  signature: : Characteristic (⊥ : Subgroup G)
  body: characteristic_iff_le_map.mpr fun _ϕ => bot_le

@[to_additive]

中文:
实例 botCharacteristic
  签名: : Characteristic (⊥ : Subgroup G)
  定义体: characteristic_iff_le_map.mpr fun _ϕ => bot_le

@[to_additive]

Depends on / 依赖: bot_le, characteristic_iff_le_map, characteristic_iff_le_map.mpr
-/
instance botCharacteristic : Characteristic (⊥ : Subgroup G) :=
  characteristic_iff_le_map.mpr fun _ϕ => bot_le

@[to_additive]
/--
Instance `topCharacteristic` / 实例 `topCharacteristic`

English:
instance topCharacteristic
  signature: : Characteristic (⊤ : Subgroup G)
  body: characteristic_iff_map_le.mpr fun _ϕ => le_top

@[to_additive]

中文:
实例 topCharacteristic
  签名: : Characteristic (⊤ : Subgroup G)
  定义体: characteristic_iff_map_le.mpr fun _ϕ => le_top

@[to_additive]

Depends on / 依赖: characteristic_iff_map_le, characteristic_iff_map_le.mpr, le_top
-/
instance topCharacteristic : Characteristic (⊤ : Subgroup G) :=
  characteristic_iff_map_le.mpr fun _ϕ => le_top

@[to_additive]
/--
Instance `characteristic_sup` / 实例 `characteristic_sup`

English:
instance characteristic_sup
  signature: [H.Characteristic] [K.Characteristic]
  body: by
  simp_all [characteristic_iff_map_eq, map_sup]

@[to_additive]

中文:
实例 characteristic_sup
  签名: [H.Characteristic] [K.Characteristic]
  定义体: by
  simp_all [characteristic_iff_map_eq, map_sup]

@[to_additive]

Depends on / 依赖: characteristic_iff_map_eq, map_sup
-/
instance characteristic_sup [H.Characteristic] [K.Characteristic] :
    (H ⊔ K).Characteristic := by
  simp_all [characteristic_iff_map_eq, map_sup]

@[to_additive]
/--
Instance `characteristic_iSup` / 实例 `characteristic_iSup`

English:
instance characteristic_iSup
  signature: {ι : Sort*} {H : ι -> Subgroup G} [forall i, (H i).Characteristic]
  body: by
  simp_all [characteristic_iff_map_eq, map_iSup]

@[to_additive]

中文:
实例 characteristic_iSup
  签名: {ι : Sort*} {H : ι -> Subgroup G} [对任意 i, (H i).Characteristic]
  定义体: by
  simp_all [characteristic_iff_map_eq, map_iSup]

@[to_additive]

Depends on / 依赖: characteristic_iff_map_eq, map_iSup
-/
instance characteristic_iSup {ι : Sort*} {H : ι -> Subgroup G} [forall i, (H i).Characteristic] :
    (⨆ i, H i).Characteristic := by
  simp_all [characteristic_iff_map_eq, map_iSup]

@[to_additive]
/--
theorem `characteristic_biSup` / 定理 `characteristic_biSup`

English:
theorem characteristic_biSup
  statement: {ι : Type*} {s : Set ι} {H : ι -> Subgroup G}
  proof: by
  simp [← iSup_subtype'', characteristic_iSup, h]

@[to_additive]

中文:
定理 characteristic_biSup
  结论: {ι : 类型} {s : Set ι} {H : ι -> Subgroup G}
  证明: by
  simp [← iSup_subtype'', characteristic_iSup, h]

@[to_additive]

Depends on / 依赖: characteristic_iSup, iSup_subtype
-/
theorem characteristic_biSup {ι : Type*} {s : Set ι} {H : ι -> Subgroup G}
    (h : forall i in s, (H i).Characteristic) : (⨆ i in s, H i).Characteristic := by
  simp [← iSup_subtype'', characteristic_iSup, h]

@[to_additive]
/--
theorem `characteristic_sSup` / 定理 `characteristic_sSup`

English:
theorem characteristic_sSup
  given: {Hs : Set (Subgroup G)} (h : forall H in Hs, H.Characteristic)
  proof: by
  simp [sSup_eq_iSup', characteristic_iSup, h]

@[to_additive]

中文:
定理 characteristic_sSup
  条件: {Hs : Set (Subgroup G)} (h : 对任意 H in Hs, H.Characteristic)
  证明: by
  simp [sSup_eq_iSup', characteristic_iSup, h]

@[to_additive]

Depends on / 依赖: characteristic_iSup, sSup_eq_iSup
-/
theorem characteristic_sSup {Hs : Set (Subgroup G)} (h : forall H in Hs, H.Characteristic) :
    (sSup Hs).Characteristic := by
  simp [sSup_eq_iSup', characteristic_iSup, h]

@[to_additive]
/--
Instance `characteristic_inf` / 实例 `characteristic_inf`

English:
instance characteristic_inf
  signature: [H.Characteristic] [K.Characteristic]
  body: by
  simp_all [characteristic_iff_comap_eq, comap_inf]

@[to_additive]

中文:
实例 characteristic_inf
  签名: [H.Characteristic] [K.Characteristic]
  定义体: by
  simp_all [characteristic_iff_comap_eq, comap_inf]

@[to_additive]

Depends on / 依赖: characteristic_iff_comap_eq, comap_inf
-/
instance characteristic_inf [H.Characteristic] [K.Characteristic] :
    (H ⊓ K).Characteristic := by
  simp_all [characteristic_iff_comap_eq, comap_inf]

@[to_additive]
/--
Instance `characteristic_iInf` / 实例 `characteristic_iInf`

English:
instance characteristic_iInf
  signature: {ι : Sort*} {H : ι -> Subgroup G} [forall i, (H i).Characteristic]
  body: by
  simp_all [characteristic_iff_comap_eq, comap_iInf]

@[to_additive]

中文:
实例 characteristic_iInf
  签名: {ι : Sort*} {H : ι -> Subgroup G} [对任意 i, (H i).Characteristic]
  定义体: by
  simp_all [characteristic_iff_comap_eq, comap_iInf]

@[to_additive]

Depends on / 依赖: characteristic_iff_comap_eq, comap_iInf
-/
instance characteristic_iInf {ι : Sort*} {H : ι -> Subgroup G} [forall i, (H i).Characteristic] :
    (⨅ i, H i).Characteristic := by
  simp_all [characteristic_iff_comap_eq, comap_iInf]

@[to_additive]
/--
theorem `characteristic_biInf` / 定理 `characteristic_biInf`

English:
theorem characteristic_biInf
  statement: {ι : Type*} {s : Set ι} {H : ι -> Subgroup G}
  proof: by
  simp [← iInf_subtype'', characteristic_iInf, h]

@[to_additive]

中文:
定理 characteristic_biInf
  结论: {ι : 类型} {s : Set ι} {H : ι -> Subgroup G}
  证明: by
  simp [← iInf_subtype'', characteristic_iInf, h]

@[to_additive]

Depends on / 依赖: characteristic_iInf, iInf_subtype
-/
theorem characteristic_biInf {ι : Type*} {s : Set ι} {H : ι -> Subgroup G}
    (h : forall i in s, (H i).Characteristic) : (⨅ i in s, H i).Characteristic := by
  simp [← iInf_subtype'', characteristic_iInf, h]

@[to_additive]
/--
theorem `characteristic_sInf` / 定理 `characteristic_sInf`

English:
theorem characteristic_sInf
  given: {Hs : Set (Subgroup G)} (h : forall H in Hs, H.Characteristic)
  proof: by
  simp [sInf_eq_iInf', characteristic_iInf, h]

中文:
定理 characteristic_sInf
  条件: {Hs : Set (Subgroup G)} (h : 对任意 H in Hs, H.Characteristic)
  证明: by
  simp [sInf_eq_iInf', characteristic_iInf, h]

Depends on / 依赖: characteristic_iInf, sInf_eq_iInf
-/
theorem characteristic_sInf {Hs : Set (Subgroup G)} (h : forall H in Hs, H.Characteristic) :
    (sInf Hs).Characteristic := by
  simp [sInf_eq_iInf', characteristic_iInf, h]

/-- If `H` is a characteristic subgroup of `G`, then every automorphism of `G` induces an
automorphism of `H`. -/
@[to_additive (attr := simps!)
  /-- If `H` is a characteristic additive subgroup of `G`, then every automorphism of `G` induces an
  automorphism of `H`. -/]
/--
Definition of `_root_.MulAut.characteristic` / `_root_.MulAut.characteristic` 的定义

English:
definition _root_.MulAut.characteristic
  signature: (H : Subgroup G) [H.Characteristic]
  body: { toFun := fun h => ⟨φ h, characteristic_iff_le_comap.mp inferInstance φ h.2⟩
      invFun := fun h => ⟨φ.symm h, characteristic_iff_le_comap.mp inferInstance φ.symm h.2⟩
      left_inv h := Subtype.ext (φ.symm_apply_apply h)
      right_inv h := Subtype.ext (φ.apply_symm_apply h)
      map_mul' h k

中文:
定义 _root_.MulAut.characteristic
  签名: (H : Subgroup G) [H.Characteristic]
  定义体: { toFun := fun h => ⟨φ h, characteristic_iff_le_comap.mp inferInstance φ h.2⟩
      invFun := fun h => ⟨φ.symm h, characteristic_iff_le_comap.mp inferInstance φ.symm h.2⟩
      left_inv h := Subtype.ext (φ.symm_apply_apply h)
      right_inv h := Subtype.ext (φ.apply_symm_apply h)
      map_mul' h k

Depends on / 依赖: Subtype, Subtype.ext, apply_symm_apply, characteristic_iff_le_comap, characteristic_iff_le_comap.mp, invFun, left_inv, map_mul, map_one, right_inv, symm_apply_apply
-/
def _root_.MulAut.characteristic (H : Subgroup G) [H.Characteristic] : MulAut G ->* MulAut H where
  toFun φ :=
    { toFun := fun h => ⟨φ h, characteristic_iff_le_comap.mp inferInstance φ h.2⟩
      invFun := fun h => ⟨φ.symm h, characteristic_iff_le_comap.mp inferInstance φ.symm h.2⟩
      left_inv h := Subtype.ext (φ.symm_apply_apply h)
      right_inv h := Subtype.ext (φ.apply_symm_apply h)
      map_mul' h k := Subtype.ext (map_mul φ (h : G) (k : G)) }
  map_one' := rfl
  map_mul' _ _ := rfl

/-- If `H` is a characteristic subgroup of `G` and `K` is a characteristic subgroup of `H`, then
`K` is a characteristic subgroup of `G`. -/
@[to_additive
  /-- If `H` is a characteristic additive subgroup of `G` and `K` is a characteristic additive
  subgroup of `H`, then `K` is a characteristic additive subgroup of `G`. -/]
/--
Instance `characteristic_of_characteristic_of_characteristic` / 实例 `characteristic_of_characteristic_of_characteristic`

English:
instance characteristic_of_characteristic_of_characteristic
  signature: [H.Characteristic]
  body: by
  refine characteristic_iff_map_eq.2 fun φ => ?_
have := congr_arg (map H.subtype) characteristic_iff_map_eq.1 hK (MulAut.characteristic H φ)
  simpa [Subgroup.map_map, MulAut.characteristic]

中文:
实例 characteristic_of_characteristic_of_characteristic
  签名: [H.Characteristic]
  定义体: by
  refine characteristic_iff_map_eq.2 fun φ => ?_
have := congr_arg (map H.subtype) characteristic_iff_map_eq.1 hK (MulAut.characteristic H φ)
  simpa [Subgroup.map_map, MulAut.characteristic]

Depends on / 依赖: H.subtype, MulAut, MulAut.characteristic, Subgroup, Subgroup.map_map, characteristic, characteristic_iff_map_eq, congr_arg, map_map, subtype
-/
instance characteristic_of_characteristic_of_characteristic [H.Characteristic]
    {K : Subgroup H} [hK : K.Characteristic] : (K.map H.subtype).Characteristic := by
  refine characteristic_iff_map_eq.2 fun φ => ?_
have := congr_arg (map H.subtype) characteristic_iff_map_eq.1 hK (MulAut.characteristic H φ)
  simpa [Subgroup.map_map, MulAut.characteristic]

variable (H)

section Normalizer

@[to_additive]
/--
theorem `normalizer_empty` / 定理 `normalizer_empty`

English:
theorem normalizer_empty
  statement: normalizer (∅ : Set G) = ⊤
  proof: ext fun _ => ⟨fun _ => trivial, fun _ _ => .rfl⟩

@[to_additive]

中文:
定理 normalizer_empty
  结论: normalizer (∅ : Set G) = ⊤
  证明: ext fun _ => ⟨fun _ => trivial, fun _ _ => .rfl⟩

@[to_additive]
-/
theorem normalizer_empty : normalizer (∅ : Set G) = ⊤ :=
  ext fun _ => ⟨fun _ => trivial, fun _ _ => .rfl⟩

@[to_additive]
/--
theorem `_root_.CommGroup.normalizer_eq_top` / 定理 `_root_.CommGroup.normalizer_eq_top`

English:
theorem _root_.CommGroup.normalizer_eq_top
  given: {G : Type*} [CommGroup G] (s : Set G)
  proof: by
  ext
  simp [mem_set_normalizer_iff]

@[to_additive]

中文:
定理 _root_.CommGroup.normalizer_eq_top
  条件: {G : 类型} [CommGroup G] (s : Set G)
  证明: by
  ext
  simp [mem_set_normalizer_iff]

@[to_additive]

Depends on / 依赖: mem_set_normalizer_iff
-/
theorem _root_.CommGroup.normalizer_eq_top {G : Type*} [CommGroup G] (s : Set G) :
    normalizer s = ⊤ := by
  ext
  simp [mem_set_normalizer_iff]

@[to_additive]
/--
theorem `mem_normalizer_iff_conj_image_eq` / 定理 `mem_normalizer_iff_conj_image_eq`

English:
theorem mem_normalizer_iff_conj_image_eq
  given: {s : Set G} {g : G}
  proof: by
  simp_rw [mem_set_normalizer_iff'', Set.ext_iff, Set.mem_image, MulAut.conj_apply]
  refine forall_congr' fun h => ?_
  simp_rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq, ← mul_assoc, exists_eq_right, iff_comm]

@[to_additive]

中文:
定理 mem_normalizer_iff_conj_image_eq
  条件: {s : Set G} {g : G}
  证明: by
  simp_rw [mem_set_normalizer_iff'', Set.ext_iff, Set.mem_image, MulAut.conj_apply]
  refine forall_congr' fun h => ?_
  simp_rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq, ← mul_assoc, exists_eq_right, iff_comm]

@[to_additive]

Depends on / 依赖: MulAut, MulAut.conj_apply, Set.ext_iff, Set.mem_image, conj_apply, eq_inv_mul_iff_mul_eq, exists_eq_right, ext_iff, forall_congr, iff_comm, mem_image, mem_set_normalizer_iff, mul_assoc, mul_inv_eq_iff_eq_mul, simp_rw
-/
theorem mem_normalizer_iff_conj_image_eq {s : Set G} {g : G} :
    g in normalizer s ↔ MulAut.conj g '' s = s := by
  simp_rw [mem_set_normalizer_iff'', Set.ext_iff, Set.mem_image, MulAut.conj_apply]
  refine forall_congr' fun h => ?_
  simp_rw [mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq, ← mul_assoc, exists_eq_right, iff_comm]

@[to_additive]
/--
theorem `mem_normalizer_iff_map_conj_eq` / 定理 `mem_normalizer_iff_map_conj_eq`

English:
theorem mem_normalizer_iff_map_conj_eq
  given: {H : Subgroup G} {g : G}
  proof: .trans mem_normalizer_iff_conj_image_eq (.symm SetLike.ext'_iff)

@[deprecated (since := "2026-05-12")]
alias _root_.AddSubgroup.mem_normalizer_iff_conj_image_eq :=
  AddSubgroup.mem_normalizer_iff_addConj_image_eq

@[to_additive]

中文:
定理 mem_normalizer_iff_map_conj_eq
  条件: {H : Subgroup G} {g : G}
  证明: .trans mem_normalizer_iff_conj_image_eq (.symm SetLike.ext'_iff)

@[deprecated (since := "2026-05-12")]
alias _root_.AddSubgroup.mem_normalizer_iff_conj_image_eq :=
  AddSubgroup.mem_normalizer_iff_addConj_image_eq

@[to_additive]

Depends on / 依赖: SetLike, SetLike.ext, _iff, mem_normalizer_iff_conj_image_eq
-/
theorem mem_normalizer_iff_map_conj_eq {H : Subgroup G} {g : G} :
    g in normalizer H ↔ H.map (MulAut.conj g) = H :=
  .trans mem_normalizer_iff_conj_image_eq (.symm SetLike.ext'_iff)

@[deprecated (since := "2026-05-12")]
alias _root_.AddSubgroup.mem_normalizer_iff_conj_image_eq :=
  AddSubgroup.mem_normalizer_iff_addConj_image_eq

@[to_additive]
/--
theorem `normalizer_le_normalizer_closure` / 定理 `normalizer_le_normalizer_closure`

English:
theorem normalizer_le_normalizer_closure
  given: (s : Set G)
  statement: normalizer s <= normalizer (closure s)
  proof: by
  intro g hg
  rw [mem_normalizer_iff_conj_image_eq] at hg
  rw [mem_normalizer_iff_map_conj_eq]; rw [MonoidHom.map_closure]; rw [MonoidHom.coe_coe]; rw [hg]

中文:
定理 normalizer_le_normalizer_closure
  条件: (s : Set G)
  结论: normalizer s <= normalizer (closure s)
  证明: by
  intro g hg
  rw [mem_normalizer_iff_conj_image_eq] at hg
  rw [mem_normalizer_iff_map_conj_eq]; rw [MonoidHom.map_closure]; rw [MonoidHom.coe_coe]; rw [hg]

Depends on / 依赖: MonoidHom, MonoidHom.coe_coe, MonoidHom.map_closure, coe_coe, map_closure, mem_normalizer_iff_conj_image_eq, mem_normalizer_iff_map_conj_eq
-/
theorem normalizer_le_normalizer_closure (s : Set G) : normalizer s <= normalizer (closure s) := by
  intro g hg
  rw [mem_normalizer_iff_conj_image_eq] at hg
  rw [mem_normalizer_iff_map_conj_eq]; rw [MonoidHom.map_closure]; rw [MonoidHom.coe_coe]; rw [hg]

variable {H}

@[to_additive]
/--
theorem `normalizer_eq_top_iff` / 定理 `normalizer_eq_top_iff`

English:
theorem normalizer_eq_top_iff
  statement: normalizer (H : Set G) = ⊤ ↔ H.Normal
  proof: eq_top_iff.trans
    ⟨fun h => ⟨fun a ha b => (h (mem_top b) a).mp ha⟩, fun h a _ha b =>
      ⟨fun hb => h.conj_mem b hb a, fun hb => inv_mul_cancel_left a b ▸ h.mem_comm_iff.mp hb⟩⟩

中文:
定理 normalizer_eq_top_iff
  结论: normalizer (H : Set G) = ⊤ ↔ H.Normal
  证明: eq_top_iff.trans
    ⟨fun h => ⟨fun a ha b => (h (mem_top b) a).mp ha⟩, fun h a _ha b =>
      ⟨fun hb => h.conj_mem b hb a, fun hb => inv_mul_cancel_left a b ▸ h.mem_comm_iff.mp hb⟩⟩

Depends on / 依赖: conj_mem, eq_top_iff, eq_top_iff.trans, h.conj_mem, h.mem_comm_iff.mp, inv_mul_cancel_left, mem_comm_iff, mem_top
-/
theorem normalizer_eq_top_iff : normalizer (H : Set G) = ⊤ ↔ H.Normal :=
  eq_top_iff.trans
    ⟨fun h => ⟨fun a ha b => (h (mem_top b) a).mp ha⟩, fun h a _ha b =>
      ⟨fun hb => h.conj_mem b hb a, fun hb => inv_mul_cancel_left a b ▸ h.mem_comm_iff.mp hb⟩⟩

variable (H) in
@[to_additive]
/--
theorem `normalizer_eq_top` / 定理 `normalizer_eq_top`

English:
theorem normalizer_eq_top
  given: [h : H.Normal]
  statement: normalizer (H : Set G) = ⊤
  proof: normalizer_eq_top_iff.mpr h

@[to_additive]

中文:
定理 normalizer_eq_top
  条件: [h : H.Normal]
  结论: normalizer (H : Set G) = ⊤
  证明: normalizer_eq_top_iff.mpr h

@[to_additive]

Depends on / 依赖: normalizer_eq_top_iff, normalizer_eq_top_iff.mpr
-/
theorem normalizer_eq_top [h : H.Normal] : normalizer (H : Set G) = ⊤ :=
  normalizer_eq_top_iff.mpr h

@[to_additive]
/--
theorem `normal_iff_map_conj_eq` / 定理 `normal_iff_map_conj_eq`

English:
theorem normal_iff_map_conj_eq
  statement: H.Normal ↔ forall g : G, H.map (MulAut.conj g) = H
  proof: by
  simp_rw [← normalizer_eq_top_iff, Subgroup.eq_top_iff', mem_normalizer_iff_map_conj_eq]

中文:
定理 normal_iff_map_conj_eq
  结论: H.Normal ↔ 对任意 g : G, H.map (MulAut.conj g) = H
  证明: by
  simp_rw [← normalizer_eq_top_iff, Subgroup.eq_top_iff', mem_normalizer_iff_map_conj_eq]

Depends on / 依赖: Subgroup, Subgroup.eq_top_iff, eq_top_iff, mem_normalizer_iff_map_conj_eq, normalizer_eq_top_iff, simp_rw
-/
theorem normal_iff_map_conj_eq : H.Normal ↔ forall g : G, H.map (MulAut.conj g) = H := by
  simp_rw [← normalizer_eq_top_iff, Subgroup.eq_top_iff', mem_normalizer_iff_map_conj_eq]

variable (H) in
@[to_additive]
/--
theorem `Normal.map_conj_eq` / 定理 `Normal.map_conj_eq`

English:
theorem Normal.map_conj_eq
  given: [H.Normal] (g : G)
  statement: H.map (MulAut.conj g) = H
  proof: normal_iff_map_conj_eq.mp ‹_› g

@[to_additive]

中文:
定理 Normal.map_conj_eq
  条件: [H.Normal] (g : G)
  结论: H.map (MulAut.conj g) = H
  证明: normal_iff_map_conj_eq.mp ‹_› g

@[to_additive]

Depends on / 依赖: normal_iff_map_conj_eq, normal_iff_map_conj_eq.mp
-/
theorem Normal.map_conj_eq [H.Normal] (g : G) : H.map (MulAut.conj g) = H :=
  normal_iff_map_conj_eq.mp ‹_› g

@[to_additive]
/--
theorem `le_set_normalizer_iff` / 定理 `le_set_normalizer_iff`

English:
theorem le_set_normalizer_iff
  given: {s : Set G}
  proof: by
.mp hg, fun hH h hh k => ⟨fun hk => hH h hh k hk, fun hk => ?_⟩⟩ refine ⟨fun hH h hh g hg => hH hh g
  simpa [mul_assoc] using hH h⁻¹ (inv_mem hh) _ hk

@[to_additive]

中文:
定理 le_set_normalizer_iff
  条件: {s : Set G}
  证明: by
.mp hg, fun hH h hh k => ⟨fun hk => hH h hh k hk, fun hk => ?_⟩⟩ refine ⟨fun hH h hh g hg => hH hh g
  simpa [mul_assoc] using hH h⁻¹ (inv_mem hh) _ hk

@[to_additive]

Depends on / 依赖: inv_mem, mul_assoc
-/
theorem le_set_normalizer_iff {s : Set G} :
    H <= normalizer s ↔ forall h in H, forall g in s, h * g * h⁻¹ in s := by
.mp hg, fun hH h hh k => ⟨fun hk => hH h hh k hk, fun hk => ?_⟩⟩ refine ⟨fun hH h hh g hg => hH hh g
  simpa [mul_assoc] using hH h⁻¹ (inv_mem hh) _ hk

@[to_additive]
/--
theorem `le_normalizer_iff` / 定理 `le_normalizer_iff`

English:
theorem le_normalizer_iff
  statement: H <= normalizer K ↔ forall h in H, forall k in K, h * k * h⁻¹ in K
  proof: by
.mp hg, fun hH h hh k => ⟨fun hk => hH h hh k hk, fun hk => ?_⟩⟩ refine ⟨fun hH h hh g hg => hH hh g
  simpa [mul_assoc] using hH h⁻¹ (inv_mem hh) _ hk

@[to_additive]

中文:
定理 le_normalizer_iff
  结论: H <= normalizer K ↔ 对任意 h in H, 对任意 k in K, h * k * h⁻¹ in K
  证明: by
.mp hg, fun hH h hh k => ⟨fun hk => hH h hh k hk, fun hk => ?_⟩⟩ refine ⟨fun hH h hh g hg => hH hh g
  simpa [mul_assoc] using hH h⁻¹ (inv_mem hh) _ hk

@[to_additive]

Depends on / 依赖: inv_mem, mul_assoc
-/
theorem le_normalizer_iff : H <= normalizer K ↔ forall h in H, forall k in K, h * k * h⁻¹ in K := by
.mp hg, fun hH h hh k => ⟨fun hk => hH h hh k hk, fun hk => ?_⟩⟩ refine ⟨fun hH h hh g hg => hH hh g
  simpa [mul_assoc] using hH h⁻¹ (inv_mem hh) _ hk

@[to_additive]
/--
theorem `le_normalizer_closure_iff` / 定理 `le_normalizer_closure_iff`

English:
theorem le_normalizer_closure_iff
  given: {s : Set G}
  proof: by
.mp mem_closure_of_mem hg, fun hH h hh => ?_⟩ refine ⟨fun hH h hh g hg => hH hh g
  rw [mem_normalizer_iff_map_conj_eq]; rw [MonoidHom.map_closure]
apply le_antisymm by simpa using! hH h hh
  rw [closure_le]; rw [← MonoidHom.map_closure]
  exact fun g hg => ⟨_, hH _ (inv_mem hh) g hg, by simp [mu

中文:
定理 le_normalizer_closure_iff
  条件: {s : Set G}
  证明: by
.mp mem_closure_of_mem hg, fun hH h hh => ?_⟩ refine ⟨fun hH h hh g hg => hH hh g
  rw [mem_normalizer_iff_map_conj_eq]; rw [MonoidHom.map_closure]
apply le_antisymm by simpa using! hH h hh
  rw [closure_le]; rw [← MonoidHom.map_closure]
  exact fun g hg => ⟨_, hH _ (inv_mem hh) g hg, by simp [mu

Depends on / 依赖: MonoidHom, MonoidHom.map_closure, closure_le, inv_mem, le_antisymm, map_closure, mem_closure_of_mem, mem_normalizer_iff_map_conj_eq, mul_assoc
-/
theorem le_normalizer_closure_iff {s : Set G} :
    H <= normalizer (closure s) ↔ forall h in H, forall g in s, h * g * h⁻¹ in closure s := by
.mp mem_closure_of_mem hg, fun hH h hh => ?_⟩ refine ⟨fun hH h hh g hg => hH hh g
  rw [mem_normalizer_iff_map_conj_eq]; rw [MonoidHom.map_closure]
apply le_antisymm by simpa using! hH h hh
  rw [closure_le]; rw [← MonoidHom.map_closure]
  exact fun g hg => ⟨_, hH _ (inv_mem hh) g hg, by simp [mul_assoc]⟩

variable {N : Type*} [Group N]

/-- The preimage of the normalizer is contained in the normalizer of the preimage. -/
@[to_additive /-- The preimage of the normalizer is contained in the normalizer of the preimage. -/]
/--
theorem `le_normalizer_comap` / 定理 `le_normalizer_comap`

English:
theorem le_normalizer_comap
  given: (f : N ->* G)
  proof: fun x => by
  simp only [mem_normalizer_iff, mem_comap]
  intro h n
  simp [h (f n)]

中文:
定理 le_normalizer_comap
  条件: (f : N ->* G)
  证明: fun x => by
  simp only [mem_normalizer_iff, mem_comap]
  intro h n
  simp [h (f n)]

Depends on / 依赖: mem_comap, mem_normalizer_iff
-/
theorem le_normalizer_comap (f : N ->* G) :
    (normalizer H).comap f <= normalizer (H.comap f) := fun x => by
  simp only [mem_normalizer_iff, mem_comap]
  intro h n
  simp [h (f n)]

/-- The image of the normalizer is contained in the normalizer of the image. -/
@[to_additive /-- The image of the normalizer is contained in the normalizer of the image. -/]
/--
theorem `le_normalizer_map` / 定理 `le_normalizer_map`

English:
theorem le_normalizer_map
  given: (f : G ->* N)
  statement: (normalizer H).map f <= normalizer (H.map f)
  proof: by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have : .comp (MulAut.conj (f y)) f = f.comp (MulAut.conj y) := by ext; simp -- todo: extract lemma
  rw [mem_normalizer_iff_map_conj_eq] at hy ⊢
  rw [map_map]; rw [this]; rw [← map_map]; rw [hy]

@[to_additive]

中文:
定理 le_normalizer_map
  条件: (f : G ->* N)
  结论: (normalizer H).map f <= normalizer (H.map f)
  证明: by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have : .comp (MulAut.conj (f y)) f = f.comp (MulAut.conj y) := by ext; simp -- todo: extract lemma
  rw [mem_normalizer_iff_map_conj_eq] at hy ⊢
  rw [map_map]; rw [this]; rw [← map_map]; rw [hy]

@[to_additive]

Depends on / 依赖: MulAut, MulAut.conj, Subgroup, Subgroup.mem_map.mp, extract, f.comp, map_map, mem_map, mem_normalizer_iff_map_conj_eq
-/
theorem le_normalizer_map (f : G ->* N) : (normalizer H).map f <= normalizer (H.map f) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  have : .comp (MulAut.conj (f y)) f = f.comp (MulAut.conj y) := by ext; simp -- todo: extract lemma
  rw [mem_normalizer_iff_map_conj_eq] at hy ⊢
  rw [map_map]; rw [this]; rw [← map_map]; rw [hy]

@[to_additive]
/--
theorem `comap_normalizer_eq_of_le_range` / 定理 `comap_normalizer_eq_of_le_range`

English:
theorem comap_normalizer_eq_of_le_range
  given: {f : N ->* G} (h : H <= f.range)
  proof: by
  apply le_antisymm (le_normalizer_comap f)
  rw [← map_le_iff_le_comap]
  apply (le_normalizer_map f).trans
  rw [map_comap_eq_self h]

@[to_additive]

中文:
定理 comap_normalizer_eq_of_le_range
  条件: {f : N ->* G} (h : H <= f.range)
  证明: by
  apply le_antisymm (le_normalizer_comap f)
  rw [← map_le_iff_le_comap]
  apply (le_normalizer_map f).trans
  rw [map_comap_eq_self h]

@[to_additive]

Depends on / 依赖: le_antisymm, le_normalizer_comap, le_normalizer_map, map_comap_eq_self, map_le_iff_le_comap
-/
theorem comap_normalizer_eq_of_le_range {f : N ->* G} (h : H <= f.range) :
    (normalizer H).comap f = normalizer (H.comap f) := by
  apply le_antisymm (le_normalizer_comap f)
  rw [← map_le_iff_le_comap]
  apply (le_normalizer_map f).trans
  rw [map_comap_eq_self h]

@[to_additive]
/--
theorem `subgroupOf_normalizer_eq` / 定理 `subgroupOf_normalizer_eq`

English:
theorem subgroupOf_normalizer_eq
  given: {H N : Subgroup G} (h : H <= N)
  proof: comap_normalizer_eq_of_le_range (h.trans_eq N.range_subtype.symm)

@[to_additive]

中文:
定理 subgroupOf_normalizer_eq
  条件: {H N : Subgroup G} (h : H <= N)
  证明: comap_normalizer_eq_of_le_range (h.trans_eq N.range_subtype.symm)

@[to_additive]

Depends on / 依赖: N.range_subtype.symm, comap_normalizer_eq_of_le_range, h.trans_eq, range_subtype, trans_eq
-/
theorem subgroupOf_normalizer_eq {H N : Subgroup G} (h : H <= N) :
    (normalizer H).subgroupOf N = normalizer (H.subgroupOf N) :=
  comap_normalizer_eq_of_le_range (h.trans_eq N.range_subtype.symm)

@[to_additive]
/--
theorem `normal_subgroupOf_iff_le_normalizer` / 定理 `normal_subgroupOf_iff_le_normalizer`

English:
theorem normal_subgroupOf_iff_le_normalizer
  given: (h : H <= K)
  proof: by
  rw [← subgroupOf_eq_top]; rw [subgroupOf_normalizer_eq h]; rw [normalizer_eq_top_iff]

@[to_additive]

中文:
定理 normal_subgroupOf_iff_le_normalizer
  条件: (h : H <= K)
  证明: by
  rw [← subgroupOf_eq_top]; rw [subgroupOf_normalizer_eq h]; rw [normalizer_eq_top_iff]

@[to_additive]

Depends on / 依赖: normalizer_eq_top_iff, subgroupOf_eq_top, subgroupOf_normalizer_eq
-/
theorem normal_subgroupOf_iff_le_normalizer (h : H <= K) :
    (H.subgroupOf K).Normal ↔ K <= normalizer H := by
  rw [← subgroupOf_eq_top]; rw [subgroupOf_normalizer_eq h]; rw [normalizer_eq_top_iff]

@[to_additive]
/--
theorem `normal_subgroupOf_iff_le_normalizer_inf` / 定理 `normal_subgroupOf_iff_le_normalizer_inf`

English:
theorem normal_subgroupOf_iff_le_normalizer_inf
  proof: inf_subgroupOf_right H K ▸ normal_subgroupOf_iff_le_normalizer inf_le_right

@[to_additive]

中文:
定理 normal_subgroupOf_iff_le_normalizer_inf
  证明: inf_subgroupOf_right H K ▸ normal_subgroupOf_iff_le_normalizer inf_le_right

@[to_additive]

Depends on / 依赖: inf_le_right, inf_subgroupOf_right, normal_subgroupOf_iff_le_normalizer
-/
theorem normal_subgroupOf_iff_le_normalizer_inf :
    (H.subgroupOf K).Normal ↔ K <= normalizer (H ⊓ K : Subgroup G) :=
  inf_subgroupOf_right H K ▸ normal_subgroupOf_iff_le_normalizer inf_le_right

@[to_additive]
instance (priority := 100) normal_in_normalizer : (H.subgroupOf <| normalizer H).Normal :=
  (normal_subgroupOf_iff_le_normalizer H.le_normalizer).mpr le_rfl

@[to_additive]
/--
theorem `maximal_normal_subgroupOf_normalizer` / 定理 `maximal_normal_subgroupOf_normalizer`

English:
theorem maximal_normal_subgroupOf_normalizer
  statement: Maximal (H.subgroupOf · |>.Normal) (normalizer H)
  proof: ⟨inferInstance,
    fun _ hnormal hle => (normal_subgroupOf_iff_le_normalizer <| le_normalizer.trans hle).mp hnormal⟩

@[to_additive]

中文:
定理 maximal_normal_subgroupOf_normalizer
  结论: Maximal (H.subgroupOf · |>.Normal) (normalizer H)
  证明: ⟨inferInstance,
    fun _ hnormal hle => (normal_subgroupOf_iff_le_normalizer <| le_normalizer.trans hle).mp hnormal⟩

@[to_additive]

Depends on / 依赖: hnormal, le_normalizer, le_normalizer.trans, normal_subgroupOf_iff_le_normalizer
-/
theorem maximal_normal_subgroupOf_normalizer : Maximal (H.subgroupOf · |>.Normal) (normalizer H) :=
  ⟨inferInstance,
    fun _ hnormal hle => (normal_subgroupOf_iff_le_normalizer <| le_normalizer.trans hle).mp hnormal⟩

@[to_additive]
/--
theorem `le_normalizer_of_normal_subgroupOf` / 定理 `le_normalizer_of_normal_subgroupOf`

English:
theorem le_normalizer_of_normal_subgroupOf
  given: [hK : (H.subgroupOf K).Normal] (HK : H <= K)
  proof: (normal_subgroupOf_iff_le_normalizer HK).mp hK

@[to_additive]

中文:
定理 le_normalizer_of_normal_subgroupOf
  条件: [hK : (H.subgroupOf K).Normal] (HK : H <= K)
  证明: (normal_subgroupOf_iff_le_normalizer HK).mp hK

@[to_additive]

Depends on / 依赖: normal_subgroupOf_iff_le_normalizer
-/
theorem le_normalizer_of_normal_subgroupOf [hK : (H.subgroupOf K).Normal] (HK : H <= K) :
    K <= normalizer H :=
  (normal_subgroupOf_iff_le_normalizer HK).mp hK

@[to_additive]
/--
theorem `subset_normalizer_of_normal` / 定理 `subset_normalizer_of_normal`

English:
theorem subset_normalizer_of_normal
  given: {S : Set G} [hH : H.Normal]
  statement: S subseteq normalizer (H : Set G)
  proof: (@normalizer_eq_top _ _ H hH) ▸ le_top

@[to_additive]

中文:
定理 subset_normalizer_of_normal
  条件: {S : Set G} [hH : H.Normal]
  结论: S subseteq normalizer (H : Set G)
  证明: (@normalizer_eq_top _ _ H hH) ▸ le_top

@[to_additive]

Depends on / 依赖: le_top, normalizer_eq_top
-/
theorem subset_normalizer_of_normal {S : Set G} [hH : H.Normal] : S subseteq normalizer (H : Set G) :=
  (@normalizer_eq_top _ _ H hH) ▸ le_top

@[to_additive]
/--
theorem `le_normalizer_of_normal` / 定理 `le_normalizer_of_normal`

English:
theorem le_normalizer_of_normal
  given: [H.Normal]
  statement: K <= normalizer H
  proof: subset_normalizer_of_normal

@[to_additive]

中文:
定理 le_normalizer_of_normal
  条件: [H.Normal]
  结论: K <= normalizer H
  证明: subset_normalizer_of_normal

@[to_additive]

Depends on / 依赖: subset_normalizer_of_normal
-/
theorem le_normalizer_of_normal [H.Normal] : K <= normalizer H := subset_normalizer_of_normal

@[to_additive]
/--
theorem `inf_normalizer_le_normalizer_inf` / 定理 `inf_normalizer_le_normalizer_inf`

English:
theorem inf_normalizer_le_normalizer_inf
  proof: fun _ h g => and_congr (h.1 g) (h.2 g)

@[to_additive]

中文:
定理 inf_normalizer_le_normalizer_inf
  证明: fun _ h g => and_congr (h.1 g) (h.2 g)

@[to_additive]

Depends on / 依赖: and_congr
-/
theorem inf_normalizer_le_normalizer_inf :
    normalizer H ⊓ normalizer K <= normalizer ((H ⊓ K :) : Set G) :=
  fun _ h g => and_congr (h.1 g) (h.2 g)

@[to_additive]
/--
theorem `iInf_normalizer_le_normalizer_iInf` / 定理 `iInf_normalizer_le_normalizer_iInf`

English:
theorem iInf_normalizer_le_normalizer_iInf
  given: {ι : Sort*} (H : ι -> Subgroup G)
  proof: by
  grind [le_normalizer_iff, mem_iInf, mem_normalizer_iff]

中文:
定理 iInf_normalizer_le_normalizer_iInf
  条件: {ι : Sort*} (H : ι -> Subgroup G)
  证明: by
  grind [le_normalizer_iff, mem_iInf, mem_normalizer_iff]

Depends on / 依赖: le_normalizer_iff, mem_iInf, mem_normalizer_iff
-/
theorem iInf_normalizer_le_normalizer_iInf {ι : Sort*} (H : ι -> Subgroup G) :
    ⨅ i, normalizer (H i) <= normalizer ((⨅ i, H i : Subgroup G) : Set G) := by
  grind [le_normalizer_iff, mem_iInf, mem_normalizer_iff]

variable (G) in
/--
Definition of `_root_.NormalizerCondition` / `_root_.NormalizerCondition` 的定义

English:
definition _root_.NormalizerCondition
  body: forall H : Subgroup G, H < ⊤ -> H < normalizer H

中文:
定义 _root_.NormalizerCondition
  定义体: forall H : Subgroup G, H < ⊤ -> H < normalizer H

Depends on / 依赖: Subgroup, normalizer
-/
def _root_.NormalizerCondition :=
  forall H : Subgroup G, H < ⊤ -> H < normalizer H

/--
theorem `_root_.normalizerCondition_iff_only_full_group_self_normalizing` / 定理 `_root_.normalizerCondition_iff_only_full_group_self_normalizing`

English:
theorem _root_.normalizerCondition_iff_only_full_group_self_normalizing
  proof: by
  apply forall_congr'; intro H
  simp only [lt_iff_le_and_ne, le_normalizer, Ne]
  tauto

中文:
定理 _root_.normalizerCondition_iff_only_full_group_self_normalizing
  证明: by
  apply forall_congr'; intro H
  simp only [lt_iff_le_and_ne, le_normalizer, Ne]
  tauto

Depends on / 依赖: forall_congr, le_normalizer, lt_iff_le_and_ne
-/
theorem _root_.normalizerCondition_iff_only_full_group_self_normalizing :
    NormalizerCondition G ↔ forall H : Subgroup G, normalizer H = H -> H = ⊤ := by
  apply forall_congr'; intro H
  simp only [lt_iff_le_and_ne, le_normalizer, Ne]
  tauto

end Normalizer

end Subgroup

namespace Group

variable {s : Set G}

/-- Given a set `s`, `conjugatesOfSet s` is the set of all conjugates of
the elements of `s`. -/
@[to_additive /-- Given a set `s`, `addConjugatesOfSet s` is the set of all additive conjugates of
the elements of `s`. -/]
/--
Definition of `conjugatesOfSet` / `conjugatesOfSet` 的定义

English:
definition conjugatesOfSet
  signature: (s : Set G)
  body: ⋃ a in s, conjugatesOf a

@[to_additive]

中文:
定义 conjugatesOfSet
  签名: (s : Set G)
  定义体: ⋃ a in s, conjugatesOf a

@[to_additive]

Depends on / 依赖: CanLift, Submonoid, conjugatesOf
-/
def conjugatesOfSet (s : Set G) : Set G :=
  ⋃ a in s, conjugatesOf a

@[to_additive]
/--
theorem `mem_conjugatesOfSet_iff` / 定理 `mem_conjugatesOfSet_iff`

English:
theorem mem_conjugatesOfSet_iff
  given: {x : G}
  statement: x in conjugatesOfSet s ↔ exists a in s, IsConj a x
  proof: by
  rw [conjugatesOfSet]; rw [Set.mem_iUnion₂]
  simp only [conjugatesOf, isConj_iff, Set.mem_ofPred_eq, exists_prop]

@[to_additive]

中文:
定理 mem_conjugatesOfSet_iff
  条件: {x : G}
  结论: x in conjugatesOfSet s ↔ 存在 a in s, IsConj a x
  证明: by
  rw [conjugatesOfSet]; rw [Set.mem_iUnion₂]
  simp only [conjugatesOf, isConj_iff, Set.mem_ofPred_eq, exists_prop]

@[to_additive]

Depends on / 依赖: Set.mem_iUnion, Set.mem_ofPred_eq, conjugatesOf, conjugatesOfSet, exists_prop, isConj_iff, mem_ofPred_eq
-/
theorem mem_conjugatesOfSet_iff {x : G} : x in conjugatesOfSet s ↔ exists a in s, IsConj a x := by
  rw [conjugatesOfSet]; rw [Set.mem_iUnion₂]
  simp only [conjugatesOf, isConj_iff, Set.mem_ofPred_eq, exists_prop]

@[to_additive]
/--
theorem `subset_conjugatesOfSet` / 定理 `subset_conjugatesOfSet`

English:
theorem subset_conjugatesOfSet
  statement: s subseteq conjugatesOfSet s
  proof: fun (x : G) (h : x in s) =>
  mem_conjugatesOfSet_iff.2 ⟨x, h, IsConj.refl _⟩

@[to_additive]

中文:
定理 subset_conjugatesOfSet
  结论: s subseteq conjugatesOfSet s
  证明: fun (x : G) (h : x in s) =>
  mem_conjugatesOfSet_iff.2 ⟨x, h, IsConj.refl _⟩

@[to_additive]
-/
theorem subset_conjugatesOfSet : s subseteq conjugatesOfSet s := fun (x : G) (h : x in s) =>
  mem_conjugatesOfSet_iff.2 ⟨x, h, IsConj.refl _⟩

@[to_additive]
/--
theorem `conjugatesOfSet_mono` / 定理 `conjugatesOfSet_mono`

English:
theorem conjugatesOfSet_mono
  given: {s t : Set G} (h : s subseteq t)
  statement: conjugatesOfSet s subseteq conjugatesOfSet t
  proof: Set.biUnion_subset_biUnion_left h

@[to_additive]

中文:
定理 conjugatesOfSet_mono
  条件: {s t : Set G} (h : s subseteq t)
  结论: conjugatesOfSet s subseteq conjugatesOfSet t
  证明: Set.biUnion_subset_biUnion_left h

@[to_additive]

Depends on / 依赖: Set.biUnion_subset_biUnion_left, biUnion_subset_biUnion_left
-/
theorem conjugatesOfSet_mono {s t : Set G} (h : s subseteq t) : conjugatesOfSet s subseteq conjugatesOfSet t :=
  Set.biUnion_subset_biUnion_left h

@[to_additive]
/--
theorem `conjugates_subset_normal` / 定理 `conjugates_subset_normal`

English:
theorem conjugates_subset_normal
  given: {N : Subgroup G} [tn : N.Normal] {a : G} (h : a in N)
  proof: by
  rintro a hc
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact tn.conj_mem a h c

@[to_additive]

中文:
定理 conjugates_subset_normal
  条件: {N : Subgroup G} [tn : N.Normal] {a : G} (h : a in N)
  证明: by
  rintro a hc
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact tn.conj_mem a h c

@[to_additive]

Depends on / 依赖: conj_mem, isConj_iff, tn.conj_mem
-/
theorem conjugates_subset_normal {N : Subgroup G} [tn : N.Normal] {a : G} (h : a in N) :
    conjugatesOf a subseteq N := by
  rintro a hc
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact tn.conj_mem a h c

@[to_additive]
/--
theorem `conjugatesOfSet_subset` / 定理 `conjugatesOfSet_subset`

English:
theorem conjugatesOfSet_subset
  given: {s : Set G} {N : Subgroup G} [N.Normal] (h : s subseteq N)
  proof: Set.iUnion₂_subset fun _x H => conjugates_subset_normal (h H)

中文:
定理 conjugatesOfSet_subset
  条件: {s : Set G} {N : Subgroup G} [N.Normal] (h : s subseteq N)
  证明: Set.iUnion₂_subset fun _x H => conjugates_subset_normal (h H)

Depends on / 依赖: Set.iUnion, conjugates_subset_normal
-/
theorem conjugatesOfSet_subset {s : Set G} {N : Subgroup G} [N.Normal] (h : s subseteq N) :
    conjugatesOfSet s subseteq N :=
  Set.iUnion₂_subset fun _x H => conjugates_subset_normal (h H)

/-- The set of conjugates of `s` is closed under conjugation. -/
@[to_additive /-- The set of additive conjugates of `s` is closed under additive conjugation. -/]
/--
theorem `conj_mem_conjugatesOfSet` / 定理 `conj_mem_conjugatesOfSet`

English:
theorem conj_mem_conjugatesOfSet
  given: {x c : G}
  proof: fun H => by
  rcases mem_conjugatesOfSet_iff.1 H with ⟨a, h₁, h₂⟩
  exact mem_conjugatesOfSet_iff.2 ⟨a, h₁, h₂.trans (isConj_iff.2 ⟨c, rfl⟩)⟩

中文:
定理 conj_mem_conjugatesOfSet
  条件: {x c : G}
  证明: fun H => by
  rcases mem_conjugatesOfSet_iff.1 H with ⟨a, h₁, h₂⟩
  exact mem_conjugatesOfSet_iff.2 ⟨a, h₁, h₂.trans (isConj_iff.2 ⟨c, rfl⟩)⟩

Depends on / 依赖: isConj_iff, mem_conjugatesOfSet_iff
-/
theorem conj_mem_conjugatesOfSet {x c : G} :
    x in conjugatesOfSet s -> c * x * c⁻¹ in conjugatesOfSet s := fun H => by
  rcases mem_conjugatesOfSet_iff.1 H with ⟨a, h₁, h₂⟩
  exact mem_conjugatesOfSet_iff.2 ⟨a, h₁, h₂.trans (isConj_iff.2 ⟨c, rfl⟩)⟩

/-- The set of conjugates of the union of two sets is the union of the conjugates -/
@[to_additive /-- The set of additive conjugates of the union of two sets is the union
of the additive conjugates. -/]
/--
theorem `conjugatesOfSet_union` / 定理 `conjugatesOfSet_union`

English:
theorem conjugatesOfSet_union
  given: {G : Type*} [Group G] (s t : Set G)
  proof: by
  simp_rw [conjugatesOfSet, Set.biUnion_union]

中文:
定理 conjugatesOfSet_union
  条件: {G : 类型} [Group G] (s t : Set G)
  证明: by
  simp_rw [conjugatesOfSet, Set.biUnion_union]

Depends on / 依赖: Set.biUnion_union, biUnion_union, conjugatesOfSet, simp_rw
-/
theorem conjugatesOfSet_union {G : Type*} [Group G] (s t : Set G) :
    conjugatesOfSet (s union t) = conjugatesOfSet s union conjugatesOfSet t := by
  simp_rw [conjugatesOfSet, Set.biUnion_union]

end Group

namespace Subgroup

open Group

variable {s : Set G}

/-- The normal closure of a set `s` is the subgroup closure of all the conjugates of
elements of `s`. It is the smallest normal subgroup containing `s`. -/
@[to_additive /-- The normal closure of a set `s` is the closure of all the additive conjugates of
elements of `s`. It is the smallest normal additive subgroup containing `s`. -/]
/--
Definition of `normalClosure` / `normalClosure` 的定义

English:
definition normalClosure
  signature: (s : Set G)
  body: closure (conjugatesOfSet s)

@[to_additive]

中文:
定义 normalClosure
  签名: (s : Set G)
  定义体: closure (conjugatesOfSet s)

@[to_additive]

Depends on / 依赖: closure, conjugatesOfSet
-/
def normalClosure (s : Set G) : Subgroup G :=
  closure (conjugatesOfSet s)

@[to_additive]
/--
theorem `conjugatesOfSet_subset_normalClosure` / 定理 `conjugatesOfSet_subset_normalClosure`

English:
theorem conjugatesOfSet_subset_normalClosure
  statement: conjugatesOfSet s subseteq normalClosure s
  proof: subset_closure

@[to_additive]

中文:
定理 conjugatesOfSet_subset_normalClosure
  结论: conjugatesOfSet s subseteq normalClosure s
  证明: subset_closure

@[to_additive]

Depends on / 依赖: subset_closure
-/
theorem conjugatesOfSet_subset_normalClosure : conjugatesOfSet s subseteq normalClosure s :=
  subset_closure

@[to_additive]
/--
theorem `subset_normalClosure` / 定理 `subset_normalClosure`

English:
theorem subset_normalClosure
  statement: s subseteq normalClosure s
  proof: Set.Subset.trans subset_conjugatesOfSet conjugatesOfSet_subset_normalClosure

@[to_additive]

中文:
定理 subset_normalClosure
  结论: s subseteq normalClosure s
  证明: Set.Subset.trans subset_conjugatesOfSet conjugatesOfSet_subset_normalClosure

@[to_additive]

Depends on / 依赖: Set.Subset.trans, Subset, conjugatesOfSet_subset_normalClosure, subset_conjugatesOfSet
-/
theorem subset_normalClosure : s subseteq normalClosure s :=
  Set.Subset.trans subset_conjugatesOfSet conjugatesOfSet_subset_normalClosure

@[to_additive]
/--
theorem `le_normalClosure` / 定理 `le_normalClosure`

English:
theorem le_normalClosure
  given: {H : Subgroup G}
  statement: H <= normalClosure ↑H
  proof: fun _ h =>
  subset_normalClosure h

中文:
定理 le_normalClosure
  条件: {H : Subgroup G}
  结论: H <= normalClosure ↑H
  证明: fun _ h =>
  subset_normalClosure h
-/
theorem le_normalClosure {H : Subgroup G} : H <= normalClosure ↑H := fun _ h =>
  subset_normalClosure h

/-- The normal closure of `s` is a normal subgroup. -/
@[to_additive /-- The normal closure of `s` is a normal additive subgroup. -/]
/--
Instance `normalClosure_normal` / 实例 `normalClosure_normal`

English:
instance normalClosure_normal
  signature: : (normalClosure s).Normal
  body: ⟨fun n h g => by
    refine Subgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_)
      (fun x _ ihx => ?_) h
    · exact conjugatesOfSet_subset_normalClosure (conj_mem_conjugatesOfSet hx)
    · simp
    · rw [← conj_mul]
      exact mul_mem ihx ihy
    · rw [← conj_inv]
      e

中文:
实例 normalClosure_normal
  签名: : (normalClosure s).Normal
  定义体: ⟨fun n h g => by
    refine Subgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_)
      (fun x _ ihx => ?_) h
    · exact conjugatesOfSet_subset_normalClosure (conj_mem_conjugatesOfSet hx)
    · simp
    · rw [← conj_mul]
      exact mul_mem ihx ihy
    · rw [← conj_inv]
      e

Depends on / 依赖: Subgroup, Subgroup.closure_induction, closure_induction, conj_inv, conj_mem_conjugatesOfSet, conj_mul, conjugatesOfSet_subset_normalClosure, inv_mem, mul_mem
-/
instance normalClosure_normal : (normalClosure s).Normal :=
  ⟨fun n h g => by
    refine Subgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_)
      (fun x _ ihx => ?_) h
    · exact conjugatesOfSet_subset_normalClosure (conj_mem_conjugatesOfSet hx)
    · simp
    · rw [← conj_mul]
      exact mul_mem ihx ihy
    · rw [← conj_inv]
      exact inv_mem ihx⟩

/-- The normal closure of `s` is the smallest normal subgroup containing `s`. -/
@[to_additive /-- The normal closure of `s` is the smallest normal additive subgroup containing`s`.
-/]
/--
theorem `normalClosure_le_normal` / 定理 `normalClosure_le_normal`

English:
theorem normalClosure_le_normal
  given: {N : Subgroup G} [N.Normal] (h : s subseteq N)
  statement: normalClosure s <= N
  proof: by
  intro a w
  refine closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) w
  · exact conjugatesOfSet_subset h hx
  · exact one_mem _
  · exact mul_mem ihx ihy
  · exact inv_mem ihx

@[to_additive]

中文:
定理 normalClosure_le_normal
  条件: {N : Subgroup G} [N.Normal] (h : s subseteq N)
  结论: normalClosure s <= N
  证明: by
  intro a w
  refine closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) w
  · exact conjugatesOfSet_subset h hx
  · exact one_mem _
  · exact mul_mem ihx ihy
  · exact inv_mem ihx

@[to_additive]

Depends on / 依赖: closure_induction, conjugatesOfSet_subset, inv_mem, mul_mem, one_mem
-/
theorem normalClosure_le_normal {N : Subgroup G} [N.Normal] (h : s subseteq N) : normalClosure s <= N := by
  intro a w
  refine closure_induction (fun x hx => ?_) ?_ (fun x y _ _ ihx ihy => ?_) (fun x _ ihx => ?_) w
  · exact conjugatesOfSet_subset h hx
  · exact one_mem _
  · exact mul_mem ihx ihy
  · exact inv_mem ihx

@[to_additive]
/--
theorem `normalClosure_subset_iff` / 定理 `normalClosure_subset_iff`

English:
theorem normalClosure_subset_iff
  given: {N : Subgroup G} [N.Normal]
  statement: s subseteq N ↔ normalClosure s <= N
  proof: ⟨normalClosure_le_normal, Set.Subset.trans subset_normalClosure⟩

@[simp]

中文:
定理 normalClosure_subset_iff
  条件: {N : Subgroup G} [N.Normal]
  结论: s subseteq N ↔ normalClosure s <= N
  证明: ⟨normalClosure_le_normal, Set.Subset.trans subset_normalClosure⟩

@[simp]

Depends on / 依赖: Set.Subset.trans, Subset, normalClosure_le_normal, subset_normalClosure
-/
theorem normalClosure_subset_iff {N : Subgroup G} [N.Normal] : s subseteq N ↔ normalClosure s <= N :=
  ⟨normalClosure_le_normal, Set.Subset.trans subset_normalClosure⟩

@[simp]
/--
theorem `normalClosure_eq_bot_iff` / 定理 `normalClosure_eq_bot_iff`

English:
theorem normalClosure_eq_bot_iff
  statement: normalClosure s = ⊥ ↔ s subseteq {1}
  proof: by
  rw [eq_bot_iff]; rw [← normalClosure_subset_iff]; rw [coe_bot]

@[to_additive (attr := gcongr)]

中文:
定理 normalClosure_eq_bot_iff
  结论: normalClosure s = ⊥ ↔ s subseteq {1}
  证明: by
  rw [eq_bot_iff]; rw [← normalClosure_subset_iff]; rw [coe_bot]

@[to_additive (attr := gcongr)]

Depends on / 依赖: coe_bot, eq_bot_iff, normalClosure_subset_iff
-/
theorem normalClosure_eq_bot_iff : normalClosure s = ⊥ ↔ s subseteq {1} := by
  rw [eq_bot_iff]; rw [← normalClosure_subset_iff]; rw [coe_bot]

@[to_additive (attr := gcongr)]
/--
theorem `normalClosure_mono` / 定理 `normalClosure_mono`

English:
theorem normalClosure_mono
  given: {s t : Set G} (h : s subseteq t)
  statement: normalClosure s <= normalClosure t
  proof: normalClosure_le_normal (Set.Subset.trans h subset_normalClosure)

@[to_additive]

中文:
定理 normalClosure_mono
  条件: {s t : Set G} (h : s subseteq t)
  结论: normalClosure s <= normalClosure t
  证明: normalClosure_le_normal (Set.Subset.trans h subset_normalClosure)

@[to_additive]

Depends on / 依赖: Set.Subset.trans, Subset, normalClosure_le_normal, subset_normalClosure
-/
theorem normalClosure_mono {s t : Set G} (h : s subseteq t) : normalClosure s <= normalClosure t :=
  normalClosure_le_normal (Set.Subset.trans h subset_normalClosure)

@[to_additive]
/--
theorem `normalClosure_eq_iInf` / 定理 `normalClosure_eq_iInf`

English:
theorem normalClosure_eq_iInf
  proof: le_antisymm (le_iInf fun _ => le_iInf fun _ => le_iInf normalClosure_le_normal)
    (iInf_le_of_le (normalClosure s)
      (iInf_le_of_le (by infer_instance) (iInf_le_of_le subset_normalClosure le_rfl)))

@[to_additive (attr := simp)]

中文:
定理 normalClosure_eq_iInf
  证明: le_antisymm (le_iInf fun _ => le_iInf fun _ => le_iInf normalClosure_le_normal)
    (iInf_le_of_le (normalClosure s)
      (iInf_le_of_le (by infer_instance) (iInf_le_of_le subset_normalClosure le_rfl)))

@[to_additive (attr := simp)]

Depends on / 依赖: iInf_le_of_le, infer_instance, le_antisymm, le_iInf, le_rfl, normalClosure, normalClosure_le_normal, subset_normalClosure
-/
theorem normalClosure_eq_iInf :
    normalClosure s = ⨅ (N : Subgroup G) (_ : Normal N) (_ : s subseteq N), N :=
  le_antisymm (le_iInf fun _ => le_iInf fun _ => le_iInf normalClosure_le_normal)
    (iInf_le_of_le (normalClosure s)
      (iInf_le_of_le (by infer_instance) (iInf_le_of_le subset_normalClosure le_rfl)))

@[to_additive (attr := simp)]
/--
theorem `normalClosure_eq_self` / 定理 `normalClosure_eq_self`

English:
theorem normalClosure_eq_self
  given: (H : Subgroup G) [H.Normal]
  statement: normalClosure ↑H = H
  proof: le_antisymm (normalClosure_le_normal rfl.subset) le_normalClosure

@[to_additive]

中文:
定理 normalClosure_eq_self
  条件: (H : Subgroup G) [H.Normal]
  结论: normalClosure ↑H = H
  证明: le_antisymm (normalClosure_le_normal rfl.subset) le_normalClosure

@[to_additive]

Depends on / 依赖: le_antisymm, le_normalClosure, normalClosure_le_normal, rfl.subset, subset
-/
theorem normalClosure_eq_self (H : Subgroup G) [H.Normal] : normalClosure ↑H = H :=
  le_antisymm (normalClosure_le_normal rfl.subset) le_normalClosure

@[to_additive]
/--
theorem `normalClosure_idempotent` / 定理 `normalClosure_idempotent`

English:
theorem normalClosure_idempotent
  statement: normalClosure ↑(normalClosure s) = normalClosure s
  proof: normalClosure_eq_self _

@[to_additive]

中文:
定理 normalClosure_idempotent
  结论: normalClosure ↑(normalClosure s) = normalClosure s
  证明: normalClosure_eq_self _

@[to_additive]

Depends on / 依赖: normalClosure_eq_self
-/
theorem normalClosure_idempotent : normalClosure ↑(normalClosure s) = normalClosure s :=
  normalClosure_eq_self _

@[to_additive]
/--
theorem `closure_le_normalClosure` / 定理 `closure_le_normalClosure`

English:
theorem closure_le_normalClosure
  given: {s : Set G}
  statement: closure s <= normalClosure s
  proof: by
  simp only [subset_normalClosure, closure_le]

@[to_additive (attr := simp)]

中文:
定理 closure_le_normalClosure
  条件: {s : Set G}
  结论: closure s <= normalClosure s
  证明: by
  simp only [subset_normalClosure, closure_le]

@[to_additive (attr := simp)]

Depends on / 依赖: closure_le, subset_normalClosure
-/
theorem closure_le_normalClosure {s : Set G} : closure s <= normalClosure s := by
  simp only [subset_normalClosure, closure_le]

@[to_additive (attr := simp)]
/--
theorem `normalClosure_closure_eq_normalClosure` / 定理 `normalClosure_closure_eq_normalClosure`

English:
theorem normalClosure_closure_eq_normalClosure
  given: {s : Set G}
  proof: le_antisymm (normalClosure_le_normal closure_le_normalClosure) (normalClosure_mono subset_closure)

中文:
定理 normalClosure_closure_eq_normalClosure
  条件: {s : Set G}
  证明: le_antisymm (normalClosure_le_normal closure_le_normalClosure) (normalClosure_mono subset_closure)

Depends on / 依赖: closure_le_normalClosure, le_antisymm, normalClosure_le_normal, normalClosure_mono, subset_closure
-/
theorem normalClosure_closure_eq_normalClosure {s : Set G} :
    normalClosure ↑(closure s) = normalClosure s :=
  le_antisymm (normalClosure_le_normal closure_le_normalClosure) (normalClosure_mono subset_closure)

/-- The normal closure of an empty set is the trivial subgroup. -/
@[to_additive (attr := simp)]
/--
lemma `normalClosure_empty` / 引理 `normalClosure_empty`

English:
lemma normalClosure_empty
  statement: normalClosure (∅ : Set G) = (⊥ : Subgroup G)
  proof: by
  rw [← normalClosure_closure_eq_normalClosure]; rw [closure_empty]; rw [normalClosure_eq_self]

中文:
引理 normalClosure_empty
  结论: normalClosure (∅ : Set G) = (⊥ : Subgroup G)
  证明: by
  rw [← normalClosure_closure_eq_normalClosure]; rw [closure_empty]; rw [normalClosure_eq_self]

Depends on / 依赖: closure_empty, normalClosure_closure_eq_normalClosure, normalClosure_eq_self
-/
lemma normalClosure_empty : normalClosure (∅ : Set G) = (⊥ : Subgroup G) := by
  rw [← normalClosure_closure_eq_normalClosure]; rw [closure_empty]; rw [normalClosure_eq_self]

/-- The normal closure of the union of sets is the join of the normal closures of each set. -/
@[to_additive]
/--
theorem `normalClosure_union` / 定理 `normalClosure_union`

English:
theorem normalClosure_union
  given: {G : Type*} [Group G] (s t : Set G)
  proof: by
  simp_rw [normalClosure, Group.conjugatesOfSet_union, closure_union]

中文:
定理 normalClosure_union
  条件: {G : 类型} [Group G] (s t : Set G)
  证明: by
  simp_rw [normalClosure, Group.conjugatesOfSet_union, closure_union]

Depends on / 依赖: Group.conjugatesOfSet_union, closure_union, conjugatesOfSet_union, normalClosure, simp_rw
-/
theorem normalClosure_union {G : Type*} [Group G] (s t : Set G) :
    normalClosure (s union t) = normalClosure s ⊔ normalClosure t := by
  simp_rw [normalClosure, Group.conjugatesOfSet_union, closure_union]

/-- The normal core of a subgroup `H` is the largest normal subgroup of `G` contained in `H`,
as shown by `Subgroup.normalCore_eq_iSup`. -/
@[to_additive /-- The normal core of an additive subgroup `H` is the largest normal additive
subgroup of `G` contained in `H`, as shown by `AddSubgroup.normalCore_eq_iSup`. -/]
/--
Definition of `normalCore` / `normalCore` 的定义

English:
definition normalCore
  signature: (H : Subgroup G)
  body: { a : G | forall b : G, b * a * b⁻¹ in H }
  one_mem' a := by rw [mul_one, mul_inv_cancel]; exact H.one_mem
  inv_mem' {_} h b := (congr_arg (· in H) conj_inv).mp (H.inv_mem (h b))
  mul_mem' {_ _} ha hb c := (congr_arg (· in H) conj_mul).mp (H.mul_mem (ha c) (hb c))

@[to_additive]

中文:
定义 normalCore
  签名: (H : Subgroup G)
  定义体: { a : G | forall b : G, b * a * b⁻¹ in H }
  one_mem' a := by rw [mul_one, mul_inv_cancel]; exact H.one_mem
  inv_mem' {_} h b := (congr_arg (· in H) conj_inv).mp (H.inv_mem (h b))
  mul_mem' {_ _} ha hb c := (congr_arg (· in H) conj_mul).mp (H.mul_mem (ha c) (hb c))

@[to_additive]
-/
def normalCore (H : Subgroup G) : Subgroup G where
  carrier := { a : G | forall b : G, b * a * b⁻¹ in H }
  one_mem' a := by rw [mul_one, mul_inv_cancel]; exact H.one_mem
  inv_mem' {_} h b := (congr_arg (· in H) conj_inv).mp (H.inv_mem (h b))
  mul_mem' {_ _} ha hb c := (congr_arg (· in H) conj_mul).mp (H.mul_mem (ha c) (hb c))

@[to_additive]
/--
theorem `normalCore_le` / 定理 `normalCore_le`

English:
theorem normalCore_le
  given: (H : Subgroup G)
  statement: H.normalCore <= H
  proof: fun a h => by
  rw [← mul_one a]; rw [← inv_one]; rw [← one_mul a]
  exact h 1

@[to_additive]

中文:
定理 normalCore_le
  条件: (H : Subgroup G)
  结论: H.normalCore <= H
  证明: fun a h => by
  rw [← mul_one a]; rw [← inv_one]; rw [← one_mul a]
  exact h 1

@[to_additive]

Depends on / 依赖: inv_one, mul_one, one_mul
-/
theorem normalCore_le (H : Subgroup G) : H.normalCore <= H := fun a h => by
  rw [← mul_one a]; rw [← inv_one]; rw [← one_mul a]
  exact h 1

@[to_additive]
/--
Instance `normalCore_normal` / 实例 `normalCore_normal`

English:
instance normalCore_normal
  signature: (H : Subgroup G)
  body: ⟨fun a h b c => by
    rw [mul_assoc]; rw [mul_assoc]; rw [← mul_inv_rev]; rw [← mul_assoc]; rw [← mul_assoc]; exact h (c * b)⟩

@[to_additive]

中文:
实例 normalCore_normal
  签名: (H : Subgroup G)
  定义体: ⟨fun a h b c => by
    rw [mul_assoc]; rw [mul_assoc]; rw [← mul_inv_rev]; rw [← mul_assoc]; rw [← mul_assoc]; exact h (c * b)⟩

@[to_additive]

Depends on / 依赖: mul_assoc, mul_inv_rev
-/
instance normalCore_normal (H : Subgroup G) : H.normalCore.Normal :=
  ⟨fun a h b c => by
    rw [mul_assoc]; rw [mul_assoc]; rw [← mul_inv_rev]; rw [← mul_assoc]; rw [← mul_assoc]; exact h (c * b)⟩

@[to_additive]
/--
theorem `normal_le_normalCore` / 定理 `normal_le_normalCore`

English:
theorem normal_le_normalCore
  given: {H : Subgroup G} {N : Subgroup G} [hN : N.Normal]
  proof: ⟨ge_trans H.normalCore_le, fun h_le n hn g => h_le (hN.conj_mem n hn g)⟩

@[to_additive]

中文:
定理 normal_le_normalCore
  条件: {H : Subgroup G} {N : Subgroup G} [hN : N.Normal]
  证明: ⟨ge_trans H.normalCore_le, fun h_le n hn g => h_le (hN.conj_mem n hn g)⟩

@[to_additive]

Depends on / 依赖: H.normalCore_le, conj_mem, ge_trans, hN.conj_mem, h_le, normalCore_le
-/
theorem normal_le_normalCore {H : Subgroup G} {N : Subgroup G} [hN : N.Normal] :
    N <= H.normalCore ↔ N <= H :=
  ⟨ge_trans H.normalCore_le, fun h_le n hn g => h_le (hN.conj_mem n hn g)⟩

@[to_additive]
/--
theorem `normalCore_mono` / 定理 `normalCore_mono`

English:
theorem normalCore_mono
  given: {H K : Subgroup G} (h : H <= K)
  statement: H.normalCore <= K.normalCore
  proof: normal_le_normalCore.mpr (H.normalCore_le.trans h)

@[to_additive]

中文:
定理 normalCore_mono
  条件: {H K : Subgroup G} (h : H <= K)
  结论: H.normalCore <= K.normalCore
  证明: normal_le_normalCore.mpr (H.normalCore_le.trans h)

@[to_additive]

Depends on / 依赖: H.normalCore_le.trans, normalCore_le, normal_le_normalCore, normal_le_normalCore.mpr
-/
theorem normalCore_mono {H K : Subgroup G} (h : H <= K) : H.normalCore <= K.normalCore :=
  normal_le_normalCore.mpr (H.normalCore_le.trans h)

@[to_additive]
/--
theorem `normalCore_eq_iSup` / 定理 `normalCore_eq_iSup`

English:
theorem normalCore_eq_iSup
  given: (H : Subgroup G)
  proof: le_antisymm
    (le_iSup_of_le H.normalCore
      (le_iSup_of_le H.normalCore_normal (le_iSup_of_le H.normalCore_le le_rfl)))
    (iSup_le fun _ => iSup_le fun _ => iSup_le normal_le_normalCore.mpr)

@[to_additive (attr := simp)]

中文:
定理 normalCore_eq_iSup
  条件: (H : Subgroup G)
  证明: le_antisymm
    (le_iSup_of_le H.normalCore
      (le_iSup_of_le H.normalCore_normal (le_iSup_of_le H.normalCore_le le_rfl)))
    (iSup_le fun _ => iSup_le fun _ => iSup_le normal_le_normalCore.mpr)

@[to_additive (attr := simp)]

Depends on / 依赖: H.normalCore, H.normalCore_le, H.normalCore_normal, iSup_le, le_antisymm, le_iSup_of_le, le_rfl, normalCore, normalCore_le, normalCore_normal, normal_le_normalCore, normal_le_normalCore.mpr
-/
theorem normalCore_eq_iSup (H : Subgroup G) :
    H.normalCore = ⨆ (N : Subgroup G) (_ : Normal N) (_ : N <= H), N :=
  le_antisymm
    (le_iSup_of_le H.normalCore
      (le_iSup_of_le H.normalCore_normal (le_iSup_of_le H.normalCore_le le_rfl)))
    (iSup_le fun _ => iSup_le fun _ => iSup_le normal_le_normalCore.mpr)

@[to_additive (attr := simp)]
/--
theorem `normalCore_eq_self` / 定理 `normalCore_eq_self`

English:
theorem normalCore_eq_self
  given: (H : Subgroup G) [H.Normal]
  statement: H.normalCore = H
  proof: le_antisymm H.normalCore_le (normal_le_normalCore.mpr le_rfl)

@[to_additive]

中文:
定理 normalCore_eq_self
  条件: (H : Subgroup G) [H.Normal]
  结论: H.normalCore = H
  证明: le_antisymm H.normalCore_le (normal_le_normalCore.mpr le_rfl)

@[to_additive]

Depends on / 依赖: H.normalCore_le, le_antisymm, le_rfl, normalCore_le, normal_le_normalCore, normal_le_normalCore.mpr
-/
theorem normalCore_eq_self (H : Subgroup G) [H.Normal] : H.normalCore = H :=
  le_antisymm H.normalCore_le (normal_le_normalCore.mpr le_rfl)

@[to_additive]
/--
theorem `normalCore_idempotent` / 定理 `normalCore_idempotent`

English:
theorem normalCore_idempotent
  given: (H : Subgroup G)
  statement: H.normalCore.normalCore = H.normalCore
  proof: H.normalCore.normalCore_eq_self

@[to_additive]

中文:
定理 normalCore_idempotent
  条件: (H : Subgroup G)
  结论: H.normalCore.normalCore = H.normalCore
  证明: H.normalCore.normalCore_eq_self

@[to_additive]

Depends on / 依赖: H.normalCore.normalCore_eq_self, normalCore, normalCore_eq_self
-/
theorem normalCore_idempotent (H : Subgroup G) : H.normalCore.normalCore = H.normalCore :=
  H.normalCore.normalCore_eq_self

@[to_additive]
/--
theorem `normalCore_eq_iInf_map_conj` / 定理 `normalCore_eq_iInf_map_conj`

English:
theorem normalCore_eq_iInf_map_conj
  given: (H : Subgroup G)
  proof: by
  have : (⨅ g : G, H.map (MulAut.conj g) : Subgroup G).Normal := by
    refine normal_iff_map_conj_eq.mpr fun g => ?_
    conv_rhs => rw [← Equiv.iInf_comp (Equiv.mulLeft g)]
    rw [map_iInf _ (MulAut.conj g).injective]
    simp [map_map, MulAut.mul_def]
  refine le_antisymm (le_iInf fun g => ?_

中文:
定理 normalCore_eq_iInf_map_conj
  条件: (H : Subgroup G)
  证明: by
  have : (⨅ g : G, H.map (MulAut.conj g) : Subgroup G).Normal := by
    refine normal_iff_map_conj_eq.mpr fun g => ?_
    conv_rhs => rw [← Equiv.iInf_comp (Equiv.mulLeft g)]
    rw [map_iInf _ (MulAut.conj g).injective]
    simp [map_map, MulAut.mul_def]
  refine le_antisymm (le_iInf fun g => ?_

Depends on / 依赖: Equiv.iInf_comp, Equiv.mulLeft, H.map, H.normalCore, MulAut, MulAut.conj, MulAut.mul_def, MulAut.one_def, Normal, Normal.map_conj_eq, Subgroup, conv_rhs, iInf_comp, iInf_le_of_le, injective, le_antisymm, le_iInf, map_conj_eq, map_iInf, map_map
-/
theorem normalCore_eq_iInf_map_conj (H : Subgroup G) :
    H.normalCore = ⨅ g : G, H.map (MulAut.conj g) := by
  have : (⨅ g : G, H.map (MulAut.conj g) : Subgroup G).Normal := by
    refine normal_iff_map_conj_eq.mpr fun g => ?_
    conv_rhs => rw [← Equiv.iInf_comp (Equiv.mulLeft g)]
    rw [map_iInf _ (MulAut.conj g).injective]
    simp [map_map, MulAut.mul_def]
  refine le_antisymm (le_iInf fun g => ?_) ?_
  · grw [← Normal.map_conj_eq H.normalCore g, normalCore_le]
  · rw [normal_le_normalCore]
    apply iInf_le_of_le 1
    simp [MulAut.one_def]

@[to_additive]
/--
theorem `normalCore_eq_iInf_comap_conj` / 定理 `normalCore_eq_iInf_comap_conj`

English:
theorem normalCore_eq_iInf_comap_conj
  given: (H : Subgroup G)
  proof: by
  rw [← (Equiv.inv G).iInf_comp]; rw [normalCore_eq_iInf_map_conj]
  simp [MulAut.inv_def, map_equiv_eq_comap_symm]

中文:
定理 normalCore_eq_iInf_comap_conj
  条件: (H : Subgroup G)
  证明: by
  rw [← (Equiv.inv G).iInf_comp]; rw [normalCore_eq_iInf_map_conj]
  simp [MulAut.inv_def, map_equiv_eq_comap_symm]

Depends on / 依赖: Equiv.inv, MulAut, MulAut.inv_def, iInf_comp, inv_def, map_equiv_eq_comap_symm, normalCore_eq_iInf_map_conj
-/
theorem normalCore_eq_iInf_comap_conj (H : Subgroup G) :
    H.normalCore = ⨅ g : G, H.comap (MulAut.conj g) := by
  rw [← (Equiv.inv G).iInf_comp]; rw [normalCore_eq_iInf_map_conj]
  simp [MulAut.inv_def, map_equiv_eq_comap_symm]

end Subgroup

namespace MonoidHom

variable {N : Type*} {P : Type*} [Group N] [Group P] (K : Subgroup G)

open Subgroup

section Ker

variable {M : Type*} [MulOneClass M]

@[to_additive prodMap_comap_prod]
/--
theorem `prodMap_comap_prod` / 定理 `prodMap_comap_prod`

English:
theorem prodMap_comap_prod
  statement: {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G ->* N)
  proof: SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

@[to_additive ker_prodMap]

中文:
定理 prodMap_comap_prod
  结论: {G' : 类型} {N' : 类型} [Group G'] [Group N'] (f : G ->* N)
  证明: SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

@[to_additive ker_prodMap]

Depends on / 依赖: Set.preimage_prod_map_prod, SetLike, SetLike.coe_injective, coe_injective, preimage_prod_map_prod
-/
theorem prodMap_comap_prod {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G ->* N)
    (g : G' ->* N') (S : Subgroup N) (S' : Subgroup N') :
    (S.prod S').comap (prodMap f g) = (S.comap f).prod (S'.comap g) :=
SetLike.coe_injective Set.preimage_prod_map_prod f g _ _

@[to_additive ker_prodMap]
/--
theorem `ker_prodMap` / 定理 `ker_prodMap`

English:
theorem ker_prodMap
  given: {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G ->* N) (g : G' ->* N')
  proof: by
  rw [← comap_bot]; rw [← comap_bot]; rw [← comap_bot]; rw [← prodMap_comap_prod]; rw [bot_prod_bot]

@[to_additive (attr := simp)]

中文:
定理 ker_prodMap
  条件: {G' : 类型} {N' : 类型} [Group G'] [Group N'] (f : G ->* N) (g : G' ->* N')
  证明: by
  rw [← comap_bot]; rw [← comap_bot]; rw [← comap_bot]; rw [← prodMap_comap_prod]; rw [bot_prod_bot]

@[to_additive (attr := simp)]

Depends on / 依赖: bot_prod_bot, comap_bot, prodMap_comap_prod
-/
theorem ker_prodMap {G' : Type*} {N' : Type*} [Group G'] [Group N'] (f : G ->* N) (g : G' ->* N') :
    (prodMap f g).ker = f.ker.prod g.ker := by
  rw [← comap_bot]; rw [← comap_bot]; rw [← comap_bot]; rw [← prodMap_comap_prod]; rw [bot_prod_bot]

@[to_additive (attr := simp)]
/--
lemma `ker_fst` / 引理 `ker_fst`

English:
lemma ker_fst
  statement: ker (fst G G') = .prod ⊥ ⊤
  proof: SetLike.ext fun _ => (iff_of_eq (and_true _)).symm

@[to_additive (attr := simp)]

中文:
引理 ker_fst
  结论: ker (fst G G') = .prod ⊥ ⊤
  证明: SetLike.ext fun _ => (iff_of_eq (and_true _)).symm

@[to_additive (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext, and_true, iff_of_eq
-/
lemma ker_fst : ker (fst G G') = .prod ⊥ ⊤ := SetLike.ext fun _ => (iff_of_eq (and_true _)).symm

@[to_additive (attr := simp)]
/--
lemma `ker_snd` / 引理 `ker_snd`

English:
lemma ker_snd
  statement: ker (snd G G') = .prod ⊤ ⊥
  proof: SetLike.ext fun _ => (iff_of_eq (true_and _)).symm

中文:
引理 ker_snd
  结论: ker (snd G G') = .prod ⊤ ⊥
  证明: SetLike.ext fun _ => (iff_of_eq (true_and _)).symm

Depends on / 依赖: MulOneClass, SetLike, SetLike.ext, iff_of_eq, toMulOneClass, true_and
-/
lemma ker_snd : ker (snd G G') = .prod ⊤ ⊥ := SetLike.ext fun _ => (iff_of_eq (true_and _)).symm

end Ker

@[to_additive (attr := simp) range_prodMap]
/--
lemma `range_prodMap` / 引理 `range_prodMap`

English:
lemma range_prodMap
  given: {G' N' : Type*} [Group G'] [Group N'] (f : G ->* N) (g : G' ->* N')
  proof: SetLike.coe_injective Set.range_prodMap

中文:
引理 range_prodMap
  条件: {G' N' : 类型} [Group G'] [Group N'] (f : G ->* N) (g : G' ->* N')
  证明: SetLike.coe_injective Set.range_prodMap

Depends on / 依赖: Set.range_prodMap, SetLike, SetLike.coe_injective, Subtype, Subtype.ext, coe_injective, congr_arg, mul_eq_one_symm, range_prodMap
-/
lemma range_prodMap {G' N' : Type*} [Group G'] [Group N'] (f : G ->* N) (g : G' ->* N') :
    (f.prodMap g).range = f.range.prod g.range :=
  SetLike.coe_injective Set.range_prodMap

end MonoidHom

namespace Subgroup

variable {N : Type*} [Group N] (H : Subgroup G)

@[to_additive]
/--
theorem `Normal.map` / 定理 `Normal.map`

English:
theorem Normal.map
  given: {H : Subgroup G} (h : H.Normal) (f : G ->* N) (hf : Function.Surjective f)
  proof: by
  rw [← normalizer_eq_top_iff]; rw [← top_le_iff]; rw [← f.range_eq_top_of_surjective hf]; rw [f.range_eq_map]; rw [← H.normalizer_eq_top]
  exact le_normalizer_map _

中文:
定理 Normal.map
  条件: {H : Subgroup G} (h : H.Normal) (f : G ->* N) (hf : Function.Surjective f)
  证明: by
  rw [← normalizer_eq_top_iff]; rw [← top_le_iff]; rw [← f.range_eq_top_of_surjective hf]; rw [f.range_eq_map]; rw [← H.normalizer_eq_top]
  exact le_normalizer_map _

Depends on / 依赖: H.normalizer_eq_top, Monoid, SetLike, f.range_eq_map, f.range_eq_top_of_surjective, le_normalizer_map, normalizer_eq_top, normalizer_eq_top_iff, range_eq_map, range_eq_top_of_surjective, toMonoid, top_le_iff
-/
theorem Normal.map {H : Subgroup G} (h : H.Normal) (f : G ->* N) (hf : Function.Surjective f) :
    (H.map f).Normal := by
  rw [← normalizer_eq_top_iff]; rw [← top_le_iff]; rw [← f.range_eq_top_of_surjective hf]; rw [f.range_eq_map]; rw [← H.normalizer_eq_top]
  exact le_normalizer_map _

end Subgroup

namespace Subgroup

open MonoidHom

variable {N : Type*} [Group N] (f : G ->* N)

/-- The preimage of the normalizer is equal to the normalizer of the preimage of a surjective
  function. -/
@[to_additive
      /-- The preimage of the normalizer is equal to the normalizer of the preimage of
      a surjective function. -/]
/--
theorem `comap_normalizer_eq_of_surjective` / 定理 `comap_normalizer_eq_of_surjective`

English:
theorem comap_normalizer_eq_of_surjective
  statement: (H : Subgroup G) {f : N ->* G}
  proof: comap_normalizer_eq_of_le_range fun x _ => hf x

中文:
定理 comap_normalizer_eq_of_surjective
  结论: (H : Subgroup G) {f : N ->* G}
  证明: comap_normalizer_eq_of_le_range fun x _ => hf x

Depends on / 依赖: CommMonoid, SetLike, comap_normalizer_eq_of_le_range, toCommMonoid
-/
theorem comap_normalizer_eq_of_surjective (H : Subgroup G) {f : N ->* G}
    (hf : Function.Surjective f) : (normalizer H).comap f = normalizer (H.comap f) :=
  comap_normalizer_eq_of_le_range fun x _ => hf x

/-- The image of the normalizer is equal to the normalizer of the image of an isomorphism. -/
@[to_additive
      /-- The image of the normalizer is equal to the normalizer of the image of an
      isomorphism. -/]
/--
theorem `map_equiv_normalizer_eq` / 定理 `map_equiv_normalizer_eq`

English:
theorem map_equiv_normalizer_eq
  given: (H : Subgroup G) (f : G ≃* N)
  proof: by
  ext x
  simp only [mem_normalizer_iff, mem_map_equiv]
  rw [f.toEquiv.forall_congr]
  intro
  simp

中文:
定理 map_equiv_normalizer_eq
  条件: (H : Subgroup G) (f : G ≃* N)
  证明: by
  ext x
  simp only [mem_normalizer_iff, mem_map_equiv]
  rw [f.toEquiv.forall_congr]
  intro
  simp

Depends on / 依赖: f.toEquiv.forall_congr, forall_congr, mem_map_equiv, mem_normalizer_iff, toEquiv
-/
theorem map_equiv_normalizer_eq (H : Subgroup G) (f : G ≃* N) :
    (normalizer H).map f.toMonoidHom = normalizer (H.map f.toMonoidHom) := by
  ext x
  simp only [mem_normalizer_iff, mem_map_equiv]
  rw [f.toEquiv.forall_congr]
  intro
  simp

/-- The image of the normalizer is equal to the normalizer of the image of a bijective
  function. -/
@[to_additive
      /-- The image of the normalizer is equal to the normalizer of the image of a bijective
        function. -/]
/--
theorem `map_normalizer_eq_of_bijective` / 定理 `map_normalizer_eq_of_bijective`

English:
theorem map_normalizer_eq_of_bijective
  given: (H : Subgroup G) {f : G ->* N} (hf : Function.Bijective f)
  proof: map_equiv_normalizer_eq H (MulEquiv.ofBijective f hf)

中文:
定理 map_normalizer_eq_of_bijective
  条件: (H : Subgroup G) {f : G ->* N} (hf : Function.Bijective f)
  证明: map_equiv_normalizer_eq H (MulEquiv.ofBijective f hf)

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective, map_equiv_normalizer_eq, ofBijective
-/
theorem map_normalizer_eq_of_bijective (H : Subgroup G) {f : G ->* N} (hf : Function.Bijective f) :
    (normalizer H).map f = normalizer (H.map f) :=
  map_equiv_normalizer_eq H (MulEquiv.ofBijective f hf)

end Subgroup

namespace MonoidHom

variable {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
variable (f : G₁ ->* G₂) (f_inv : G₂ -> G₁)

/-- Auxiliary definition used to define `liftOfRightInverse` -/
@[to_additive /-- Auxiliary definition used to define `liftOfRightInverse` -/]
/--
Definition of `liftOfRightInverseAux` / `liftOfRightInverseAux` 的定义

English:
definition liftOfRightInverseAux
  signature: (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃) (hg : f.ker <= g.ker)
  body: g (f_inv b)
  map_one' := hg (hf 1)
  map_mul' := by
    intro x y
    rw [← g.map_mul]; rw [← mul_inv_eq_one]; rw [← g.map_inv]; rw [← g.map_mul]; rw [← g.mem_ker]
    apply hg
    rw [f.mem_ker]; rw [f.map_mul]; rw [f.map_inv]; rw [mul_inv_eq_one]; rw [f.map_mul]
    simp only [hf _]

中文:
定义 liftOfRightInverseAux
  签名: (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃) (hg : f.ker <= g.ker)
  定义体: g (f_inv b)
  map_one' := hg (hf 1)
  map_mul' := by
    intro x y
    rw [← g.map_mul]; rw [← mul_inv_eq_one]; rw [← g.map_inv]; rw [← g.map_mul]; rw [← g.mem_ker]
    apply hg
    rw [f.mem_ker]; rw [f.map_mul]; rw [f.map_inv]; rw [mul_inv_eq_one]; rw [f.map_mul]
    simp only [hf _]

Depends on / 依赖: f_inv
-/
def liftOfRightInverseAux (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃) (hg : f.ker <= g.ker) :
    G₂ ->* G₃ where
  toFun b := g (f_inv b)
  map_one' := hg (hf 1)
  map_mul' := by
    intro x y
    rw [← g.map_mul]; rw [← mul_inv_eq_one]; rw [← g.map_inv]; rw [← g.map_mul]; rw [← g.mem_ker]
    apply hg
    rw [f.mem_ker]; rw [f.map_mul]; rw [f.map_inv]; rw [mul_inv_eq_one]; rw [f.map_mul]
    simp only [hf _]

set_option backward.isDefEq.respectTransparency false in
@[to_additive (attr := simp)]
/--
theorem `liftOfRightInverseAux_comp_apply` / 定理 `liftOfRightInverseAux_comp_apply`

English:
theorem liftOfRightInverseAux_comp_apply
  statement: (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃)
  proof: by
  dsimp [liftOfRightInverseAux]
  rw [← mul_inv_eq_one]; rw [← g.map_inv]; rw [← g.map_mul]; rw [← g.mem_ker]
  apply hg
  rw [f.mem_ker]; rw [f.map_mul]; rw [f.map_inv]; rw [mul_inv_eq_one]
  simp only [hf _]

中文:
定理 liftOfRightInverseAux_comp_apply
  结论: (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃)
  证明: by
  dsimp [liftOfRightInverseAux]
  rw [← mul_inv_eq_one]; rw [← g.map_inv]; rw [← g.map_mul]; rw [← g.mem_ker]
  apply hg
  rw [f.mem_ker]; rw [f.map_mul]; rw [f.map_inv]; rw [mul_inv_eq_one]
  simp only [hf _]

Depends on / 依赖: f.map_inv, f.map_mul, f.mem_ker, g.map_inv, g.map_mul, g.mem_ker, liftOfRightInverseAux, map_inv, map_mul, mem_ker, mul_inv_eq_one
-/
theorem liftOfRightInverseAux_comp_apply (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃)
    (hg : f.ker <= g.ker) (x : G₁) : (f.liftOfRightInverseAux f_inv hf g hg) (f x) = g x := by
  dsimp [liftOfRightInverseAux]
  rw [← mul_inv_eq_one]; rw [← g.map_inv]; rw [← g.map_mul]; rw [← g.mem_ker]
  apply hg
  rw [f.mem_ker]; rw [f.map_mul]; rw [f.map_inv]; rw [mul_inv_eq_one]
  simp only [hf _]

/-- `liftOfRightInverse f hf g hg` is the unique group homomorphism `φ`

* such that `φ.comp f = g` (`MonoidHom.liftOfRightInverse_comp`),
* where `f : G₁ →+* G₂` has a RightInverse `f_inv` (`hf`),
* and `g : G₂ →+* G₃` satisfies `hg : f.ker ≤ g.ker`.

See `MonoidHom.eq_liftOfRightInverse` for the uniqueness lemma.

```
   G₁.
   | \
 f | \ g
   | \
   v \⌟
   G₂----> G₃
      ∃!φ
```
-/
@[to_additive
      /-- `liftOfRightInverse f f_inv hf g hg` is the unique additive group homomorphism `φ`
      * such that `φ.comp f = g` (`AddMonoidHom.liftOfRightInverse_comp`),
      * where `f : G₁ →+ G₂` has a RightInverse `f_inv` (`hf`),
      * and `g : G₂ →+ G₃` satisfies `hg : f.ker ≤ g.ker`.
      See `AddMonoidHom.eq_liftOfRightInverse` for the uniqueness lemma.
      ```
         G₁.
         | \
       f | \ g
         | \
         v \⌟
         G₂----> G₃
            ∃!φ
      ``` -/]
/--
Definition of `liftOfRightInverse` / `liftOfRightInverse` 的定义

English:
definition liftOfRightInverse
  signature: (hf : Function.RightInverse f_inv f)
  body: f.liftOfRightInverseAux f_inv hf g.1 g.2
invFun φ := ⟨φ.comp f, fun x hx => mem_ker.mpr by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

中文:
定义 liftOfRightInverse
  签名: (hf : Function.RightInverse f_inv f)
  定义体: f.liftOfRightInverseAux f_inv hf g.1 g.2
invFun φ := ⟨φ.comp f, fun x hx => mem_ker.mpr by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

Depends on / 依赖: f.liftOfRightInverseAux, f_inv, liftOfRightInverseAux
-/
def liftOfRightInverse (hf : Function.RightInverse f_inv f) :
    { g : G₁ ->* G₃ // f.ker <= g.ker } ≃ (G₂ ->* G₃) where
  toFun g := f.liftOfRightInverseAux f_inv hf g.1 g.2
invFun φ := ⟨φ.comp f, fun x hx => mem_ker.mpr by simp [mem_ker.mp hx]⟩
  left_inv g := by
    ext
    simp only [comp_apply, liftOfRightInverseAux_comp_apply]
  right_inv φ := by
    ext b
    simp [liftOfRightInverseAux, hf b]

/-- A non-computable version of `MonoidHom.liftOfRightInverse` for when no computable right
inverse is available, that uses `Function.surjInv`. -/
@[to_additive (attr := simp)
      /-- A non-computable version of `AddMonoidHom.liftOfRightInverse` for when no
      computable right inverse is available. -/]
/--
Definition of `liftOfSurjective` / `liftOfSurjective` 的定义

English:
abbreviation liftOfSurjective
  signature: (hf : Function.Surjective f)
  body: f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)

@[to_additive (attr := simp)]

中文:
缩写 liftOfSurjective
  签名: (hf : Function.Surjective f)
  定义体: f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)

@[to_additive (attr := simp)]

Depends on / 依赖: Function, Function.rightInverse_surjInv, Function.surjInv, f.liftOfRightInverse, liftOfRightInverse, rightInverse_surjInv, surjInv
-/
noncomputable abbrev liftOfSurjective (hf : Function.Surjective f) :
    { g : G₁ ->* G₃ // f.ker <= g.ker } ≃ (G₂ ->* G₃) :=
  f.liftOfRightInverse (Function.surjInv hf) (Function.rightInverse_surjInv hf)

@[to_additive (attr := simp)]
/--
theorem `liftOfRightInverse_comp_apply` / 定理 `liftOfRightInverse_comp_apply`

English:
theorem liftOfRightInverse_comp_apply
  statement: (hf : Function.RightInverse f_inv f)
  proof: f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x

@[to_additive (attr := simp)]

中文:
定理 liftOfRightInverse_comp_apply
  结论: (hf : Function.RightInverse f_inv f)
  证明: f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x

@[to_additive (attr := simp)]

Depends on / 依赖: f.liftOfRightInverseAux_comp_apply, f_inv, liftOfRightInverseAux_comp_apply
-/
theorem liftOfRightInverse_comp_apply (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ ->* G₃ // f.ker <= g.ker }) (x : G₁) :
    (f.liftOfRightInverse f_inv hf g) (f x) = g.1 x :=
  f.liftOfRightInverseAux_comp_apply f_inv hf g.1 g.2 x

@[to_additive (attr := simp)]
/--
theorem `liftOfRightInverse_comp` / 定理 `liftOfRightInverse_comp`

English:
theorem liftOfRightInverse_comp
  statement: (hf : Function.RightInverse f_inv f)
  proof: MonoidHom.ext f.liftOfRightInverse_comp_apply f_inv hf g

@[to_additive]

中文:
定理 liftOfRightInverse_comp
  结论: (hf : Function.RightInverse f_inv f)
  证明: MonoidHom.ext f.liftOfRightInverse_comp_apply f_inv hf g

@[to_additive]

Depends on / 依赖: MonoidHom, MonoidHom.ext, f.liftOfRightInverse_comp_apply, f_inv, liftOfRightInverse_comp_apply
-/
theorem liftOfRightInverse_comp (hf : Function.RightInverse f_inv f)
    (g : { g : G₁ ->* G₃ // f.ker <= g.ker }) : (f.liftOfRightInverse f_inv hf g).comp f = g :=
MonoidHom.ext f.liftOfRightInverse_comp_apply f_inv hf g

@[to_additive]
/--
theorem `eq_liftOfRightInverse` / 定理 `eq_liftOfRightInverse`

English:
theorem eq_liftOfRightInverse
  statement: (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃)
  proof: by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

中文:
定理 eq_liftOfRightInverse
  结论: (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃)
  证明: by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

Depends on / 依赖: apply_symm_apply, f.liftOfRightInverse, f_inv, liftOfRightInverse, simp_rw
-/
theorem eq_liftOfRightInverse (hf : Function.RightInverse f_inv f) (g : G₁ ->* G₃)
    (hg : f.ker <= g.ker) (h : G₂ ->* G₃) (hh : h.comp f = g) :
    h = f.liftOfRightInverse f_inv hf ⟨g, hg⟩ := by
  simp_rw [← hh]
  exact ((f.liftOfRightInverse f_inv hf).apply_symm_apply _).symm

end MonoidHom

variable {N : Type*} [Group N]

namespace Subgroup

-- Here `H.Normal` is an explicit argument so we can use dot notation with `comap`.
@[to_additive]
/--
theorem `Normal.comap` / 定理 `Normal.comap`

English:
theorem Normal.comap
  given: {H : Subgroup N} (hH : H.Normal) (f : G ->* N)
  statement: (H.comap f).Normal
  proof: ⟨fun _ => by simp +contextual [Subgroup.mem_comap, hH.conj_mem]⟩

@[to_additive]

中文:
定理 Normal.comap
  条件: {H : Subgroup N} (hH : H.Normal) (f : G ->* N)
  结论: (H.comap f).Normal
  证明: ⟨fun _ => by simp +contextual [Subgroup.mem_comap, hH.conj_mem]⟩

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.mem_comap, conj_mem, contextual, hH.conj_mem, mem_comap
-/
theorem Normal.comap {H : Subgroup N} (hH : H.Normal) (f : G ->* N) : (H.comap f).Normal :=
  ⟨fun _ => by simp +contextual [Subgroup.mem_comap, hH.conj_mem]⟩

@[to_additive]
instance (priority := 100) normal_comap {H : Subgroup N} [nH : H.Normal] (f : G ->* N) :
    (H.comap f).Normal :=
  nH.comap _

-- Here `H.Normal` is an explicit argument so we can use dot notation with `subgroupOf`.
@[to_additive]
/--
theorem `Normal.subgroupOf` / 定理 `Normal.subgroupOf`

English:
theorem Normal.subgroupOf
  given: {H : Subgroup G} (hH : H.Normal) (K : Subgroup G)
  proof: hH.comap _

@[to_additive]

中文:
定理 Normal.subgroupOf
  条件: {H : Subgroup G} (hH : H.Normal) (K : Subgroup G)
  证明: hH.comap _

@[to_additive]

Depends on / 依赖: hH.comap
-/
theorem Normal.subgroupOf {H : Subgroup G} (hH : H.Normal) (K : Subgroup G) :
    (H.subgroupOf K).Normal :=
  hH.comap _

@[to_additive]
instance (priority := 100) normal_subgroupOf {H N : Subgroup G} [N.Normal] :
    (N.subgroupOf H).Normal :=
  Subgroup.normal_comap _

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/--
theorem `comap_normalClosure_image_ge` / 定理 `comap_normalClosure_image_ge`

English:
theorem comap_normalClosure_image_ge
  given: (s : Set G) (f : G ->* N)
  proof: by
  simp [normalClosure_le_normal, ← Set.image_subset_iff, subset_normalClosure]

@[to_additive]

中文:
定理 comap_normalClosure_image_ge
  条件: (s : Set G) (f : G ->* N)
  证明: by
  simp [normalClosure_le_normal, ← Set.image_subset_iff, subset_normalClosure]

@[to_additive]

Depends on / 依赖: Set.image_subset_iff, image_subset_iff, normalClosure_le_normal, subset_normalClosure
-/
theorem comap_normalClosure_image_ge (s : Set G) (f : G ->* N) :
    (normalClosure s) <= (normalClosure (f '' s)).comap f := by
  simp [normalClosure_le_normal, ← Set.image_subset_iff, subset_normalClosure]

@[to_additive]
/--
theorem `map_normalClosure_le` / 定理 `map_normalClosure_le`

English:
theorem map_normalClosure_le
  given: (s : Set G) (f : G ->* N)
  proof: by
  simp [map_le_iff_le_comap, comap_normalClosure_image_ge]

@[to_additive]

中文:
定理 map_normalClosure_le
  条件: (s : Set G) (f : G ->* N)
  证明: by
  simp [map_le_iff_le_comap, comap_normalClosure_image_ge]

@[to_additive]

Depends on / 依赖: comap_normalClosure_image_ge, map_le_iff_le_comap
-/
theorem map_normalClosure_le (s : Set G) (f : G ->* N) :
    (normalClosure s).map f <= normalClosure (f '' s) := by
  simp [map_le_iff_le_comap, comap_normalClosure_image_ge]

@[to_additive]
/--
theorem `map_normalClosure` / 定理 `map_normalClosure`

English:
theorem map_normalClosure
  given: (s : Set G) (f : G ->* N) (hf : Surjective f)
  proof: by
  have : Normal (map f (normalClosure s)) := Normal.map inferInstance f hf
  apply le_antisymm
  · exact map_normalClosure_le s f
  · exact normalClosure_le_normal (Set.image_mono subset_normalClosure)

@[to_additive]

中文:
定理 map_normalClosure
  条件: (s : Set G) (f : G ->* N) (hf : Surjective f)
  证明: by
  have : Normal (map f (normalClosure s)) := Normal.map inferInstance f hf
  apply le_antisymm
  · exact map_normalClosure_le s f
  · exact normalClosure_le_normal (Set.image_mono subset_normalClosure)

@[to_additive]

Depends on / 依赖: Normal, Normal.map, Set.image_mono, image_mono, le_antisymm, map_normalClosure_le, normalClosure, normalClosure_le_normal, subset_normalClosure
-/
theorem map_normalClosure (s : Set G) (f : G ->* N) (hf : Surjective f) :
    (normalClosure s).map f = normalClosure (f '' s) := by
  have : Normal (map f (normalClosure s)) := Normal.map inferInstance f hf
  apply le_antisymm
  · exact map_normalClosure_le s f
  · exact normalClosure_le_normal (Set.image_mono subset_normalClosure)

@[to_additive]
/--
theorem `comap_normalClosure` / 定理 `comap_normalClosure`

English:
theorem comap_normalClosure
  given: (s : Set N) (f : G ≃* N)
  proof: by
  have := f.toEquiv.image_symm_eq_preimage s
  simp_all [comap_equiv_eq_map_symm, map_normalClosure s (f.symm : N ->* G) f.symm.surjective]

中文:
定理 comap_normalClosure
  条件: (s : Set N) (f : G ≃* N)
  证明: by
  have := f.toEquiv.image_symm_eq_preimage s
  simp_all [comap_equiv_eq_map_symm, map_normalClosure s (f.symm : N ->* G) f.symm.surjective]

Depends on / 依赖: comap_equiv_eq_map_symm, f.symm, f.symm.surjective, f.toEquiv.image_symm_eq_preimage, image_symm_eq_preimage, map_normalClosure, surjective, toEquiv
-/
theorem comap_normalClosure (s : Set N) (f : G ≃* N) :
    normalClosure (f ⁻¹' s) = (normalClosure s).comap f := by
  have := f.toEquiv.image_symm_eq_preimage s
  simp_all [comap_equiv_eq_map_symm, map_normalClosure s (f.symm : N ->* G) f.symm.surjective]

/--
lemma `Normal.of_map_injective` / 引理 `Normal.of_map_injective`

English:
lemma Normal.of_map_injective
  statement: {G H : Type*} [Group G] [Group H] {φ : G ->* H}
  proof: L.comap_map_eq_self_of_injective hφ ▸ n.comap φ

中文:
引理 Normal.of_map_injective
  结论: {G H : 类型} [Group G] [Group H] {φ : G ->* H}
  证明: L.comap_map_eq_self_of_injective hφ ▸ n.comap φ

Depends on / 依赖: L.comap_map_eq_self_of_injective, comap_map_eq_self_of_injective, n.comap
-/
lemma Normal.of_map_injective {G H : Type*} [Group G] [Group H] {φ : G ->* H}
    (hφ : Function.Injective φ) {L : Subgroup G} (n : (L.map φ).Normal) : L.Normal :=
  L.comap_map_eq_self_of_injective hφ ▸ n.comap φ

/--
theorem `Normal.of_map_subtype` / 定理 `Normal.of_map_subtype`

English:
theorem Normal.of_map_subtype
  statement: {K : Subgroup G} {L : Subgroup K}
  proof: n.of_map_injective K.subtype_injective

中文:
定理 Normal.of_map_subtype
  结论: {K : Subgroup G} {L : Subgroup K}
  证明: n.of_map_injective K.subtype_injective

Depends on / 依赖: K.subtype_injective, n.of_map_injective, of_map_injective, subtype_injective
-/
theorem Normal.of_map_subtype {K : Subgroup G} {L : Subgroup K}
    (n : (Subgroup.map K.subtype L).Normal) : L.Normal :=
  n.of_map_injective K.subtype_injective

/--
theorem `normal_comap_iff_of_surjective` / 定理 `normal_comap_iff_of_surjective`

English:
theorem normal_comap_iff_of_surjective
  given: {f : G ->* N} (hf : Function.Surjective f) {H : Subgroup N}
  proof: by
  rw [← normalizer_eq_top_iff]; rw [← comap_normalizer_eq_of_surjective H hf]; rw [← comap_top f]; rw [(comap_injective hf).eq_iff]; rw [normalizer_eq_top_iff]

中文:
定理 normal_comap_iff_of_surjective
  条件: {f : G ->* N} (hf : Function.Surjective f) {H : Subgroup N}
  证明: by
  rw [← normalizer_eq_top_iff]; rw [← comap_normalizer_eq_of_surjective H hf]; rw [← comap_top f]; rw [(comap_injective hf).eq_iff]; rw [normalizer_eq_top_iff]

Depends on / 依赖: comap_injective, comap_normalizer_eq_of_surjective, comap_top, eq_iff, normalizer_eq_top_iff
-/
theorem normal_comap_iff_of_surjective {f : G ->* N} (hf : Function.Surjective f) {H : Subgroup N} :
    (H.comap f).Normal ↔ H.Normal := by
  rw [← normalizer_eq_top_iff]; rw [← comap_normalizer_eq_of_surjective H hf]; rw [← comap_top f]; rw [(comap_injective hf).eq_iff]; rw [normalizer_eq_top_iff]

/--
theorem `_root_.MulEquiv.normal_map_iff` / 定理 `_root_.MulEquiv.normal_map_iff`

English:
theorem _root_.MulEquiv.normal_map_iff
  given: {f : G ≃* G'} {H : Subgroup G}
  proof: by
  rw [map_equiv_eq_comap_symm]; rw [normal_comap_iff_of_surjective f.symm.surjective]

中文:
定理 _root_.MulEquiv.normal_map_iff
  条件: {f : G ≃* G'} {H : Subgroup G}
  证明: by
  rw [map_equiv_eq_comap_symm]; rw [normal_comap_iff_of_surjective f.symm.surjective]

Depends on / 依赖: f.symm.surjective, map_equiv_eq_comap_symm, normal_comap_iff_of_surjective, surjective
-/
theorem _root_.MulEquiv.normal_map_iff {f : G ≃* G'} {H : Subgroup G} :
    (H.map (f : G ->* G')).Normal ↔ H.Normal := by
  rw [map_equiv_eq_comap_symm]; rw [normal_comap_iff_of_surjective f.symm.surjective]

section SubgroupNormal

@[to_additive]
/--
theorem `normal_subgroupOf_iff` / 定理 `normal_subgroupOf_iff`

English:
theorem normal_subgroupOf_iff
  given: {H K : Subgroup G} (hHK : H <= K)
  proof: ⟨fun hN h k hH hK => hN.conj_mem ⟨h, hHK hH⟩ hH ⟨k, hK⟩, fun hN =>
    { conj_mem := fun h hm k => hN h.1 k.1 hm k.2 }⟩

@[to_additive prod_addSubgroupOf_prod_normal]

中文:
定理 normal_subgroupOf_iff
  条件: {H K : Subgroup G} (hHK : H <= K)
  证明: ⟨fun hN h k hH hK => hN.conj_mem ⟨h, hHK hH⟩ hH ⟨k, hK⟩, fun hN =>
    { conj_mem := fun h hm k => hN h.1 k.1 hm k.2 }⟩

@[to_additive prod_addSubgroupOf_prod_normal]

Depends on / 依赖: AddMonoid, DistribMulAction, conj_mem, hN.conj_mem
-/
theorem normal_subgroupOf_iff {H K : Subgroup G} (hHK : H <= K) :
    (H.subgroupOf K).Normal ↔ forall h k, h in H -> k in K -> k * h * k⁻¹ in H :=
  ⟨fun hN h k hH hK => hN.conj_mem ⟨h, hHK hH⟩ hH ⟨k, hK⟩, fun hN =>
    { conj_mem := fun h hm k => hN h.1 k.1 hm k.2 }⟩

@[to_additive prod_addSubgroupOf_prod_normal]
/--
Instance `prod_subgroupOf_prod_normal` / 实例 `prod_subgroupOf_prod_normal`

English:
instance prod_subgroupOf_prod_normal
  signature: {H₁ K₁ : Subgroup G} {H₂ K₂ : Subgroup N}
  body: ⟨h₁.conj_mem ⟨(n : G × N).fst, (mem_prod.mp n.2).1⟩ hgHK.1
        ⟨(g : G × N).fst, (mem_prod.mp g.2).1⟩,
      h₂.conj_mem ⟨(n : G × N).snd, (mem_prod.mp n.2).2⟩ hgHK.2
        ⟨(g : G × N).snd, (mem_prod.mp g.2).2⟩⟩

@[to_additive prod_normal]

中文:
实例 prod_subgroupOf_prod_normal
  签名: {H₁ K₁ : Subgroup G} {H₂ K₂ : Subgroup N}
  定义体: ⟨h₁.conj_mem ⟨(n : G × N).fst, (mem_prod.mp n.2).1⟩ hgHK.1
        ⟨(g : G × N).fst, (mem_prod.mp g.2).1⟩,
      h₂.conj_mem ⟨(n : G × N).snd, (mem_prod.mp n.2).2⟩ hgHK.2
        ⟨(g : G × N).snd, (mem_prod.mp g.2).2⟩⟩

@[to_additive prod_normal]

Depends on / 依赖: conj_mem, mem_prod, mem_prod.mp
-/
instance prod_subgroupOf_prod_normal {H₁ K₁ : Subgroup G} {H₂ K₂ : Subgroup N}
    [h₁ : (H₁.subgroupOf K₁).Normal] [h₂ : (H₂.subgroupOf K₂).Normal] :
    ((H₁.prod H₂).subgroupOf (K₁.prod K₂)).Normal where
  conj_mem n hgHK g :=
    ⟨h₁.conj_mem ⟨(n : G × N).fst, (mem_prod.mp n.2).1⟩ hgHK.1
        ⟨(g : G × N).fst, (mem_prod.mp g.2).1⟩,
      h₂.conj_mem ⟨(n : G × N).snd, (mem_prod.mp n.2).2⟩ hgHK.2
        ⟨(g : G × N).snd, (mem_prod.mp g.2).2⟩⟩

@[to_additive prod_normal]
/--
Instance `prod_normal` / 实例 `prod_normal`

English:
instance prod_normal
  signature: (H : Subgroup G) (K : Subgroup N) [hH : H.Normal] [hK : K.Normal]
  body: ⟨hH.conj_mem n.fst (Subgroup.mem_prod.mp hg).1 g.fst,
      hK.conj_mem n.snd (Subgroup.mem_prod.mp hg).2 g.snd⟩

@[to_additive]

中文:
实例 prod_normal
  签名: (H : Subgroup G) (K : Subgroup N) [hH : H.Normal] [hK : K.Normal]
  定义体: ⟨hH.conj_mem n.fst (Subgroup.mem_prod.mp hg).1 g.fst,
      hK.conj_mem n.snd (Subgroup.mem_prod.mp hg).2 g.snd⟩

@[to_additive]

Depends on / 依赖: Monoid, MulDistribMulAction, Subgroup, Subgroup.mem_prod.mp, conj_mem, g.fst, g.snd, hH.conj_mem, hK.conj_mem, mem_prod, n.fst, n.snd
-/
instance prod_normal (H : Subgroup G) (K : Subgroup N) [hH : H.Normal] [hK : K.Normal] :
    (H.prod K).Normal where
  conj_mem n hg g :=
    ⟨hH.conj_mem n.fst (Subgroup.mem_prod.mp hg).1 g.fst,
      hK.conj_mem n.snd (Subgroup.mem_prod.mp hg).2 g.snd⟩

@[to_additive]
/--
theorem `inf_subgroupOf_inf_normal_of_right` / 定理 `inf_subgroupOf_inf_normal_of_right`

English:
theorem inf_subgroupOf_inf_normal_of_right
  statement: (A B' B : Subgroup G)
  proof: by
  rw [normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm]; rw [inf_idem]
  exact le_trans (inf_le_inf A.le_normalizer hN) inf_normalizer_le_normalizer_inf

@[to_additive]

中文:
定理 inf_subgroupOf_inf_normal_of_right
  结论: (A B' B : Subgroup G)
  证明: by
  rw [normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm]; rw [inf_idem]
  exact le_trans (inf_le_inf A.le_normalizer hN) inf_normalizer_le_normalizer_inf

@[to_additive]

Depends on / 依赖: A.le_normalizer, inf_idem, inf_inf_inf_comm, inf_le_inf, inf_normalizer_le_normalizer_inf, le_normalizer, le_trans, normal_subgroupOf_iff_le_normalizer_inf
-/
theorem inf_subgroupOf_inf_normal_of_right (A B' B : Subgroup G)
    [hN : (B'.subgroupOf B).Normal] : ((A ⊓ B').subgroupOf (A ⊓ B)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm]; rw [inf_idem]
  exact le_trans (inf_le_inf A.le_normalizer hN) inf_normalizer_le_normalizer_inf

@[to_additive]
/--
theorem `inf_subgroupOf_inf_normal_of_left` / 定理 `inf_subgroupOf_inf_normal_of_left`

English:
theorem inf_subgroupOf_inf_normal_of_left
  statement: {A' A : Subgroup G} (B : Subgroup G)
  proof: by
  rw [normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm]; rw [inf_idem]
  exact le_trans (inf_le_inf hN B.le_normalizer) inf_normalizer_le_normalizer_inf

@[to_additive]

中文:
定理 inf_subgroupOf_inf_normal_of_left
  结论: {A' A : Subgroup G} (B : Subgroup G)
  证明: by
  rw [normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm]; rw [inf_idem]
  exact le_trans (inf_le_inf hN B.le_normalizer) inf_normalizer_le_normalizer_inf

@[to_additive]

Depends on / 依赖: B.le_normalizer, inf_idem, inf_inf_inf_comm, inf_le_inf, inf_normalizer_le_normalizer_inf, le_normalizer, le_trans, normal_subgroupOf_iff_le_normalizer_inf
-/
theorem inf_subgroupOf_inf_normal_of_left {A' A : Subgroup G} (B : Subgroup G)
    [hN : (A'.subgroupOf A).Normal] : ((A' ⊓ B).subgroupOf (A ⊓ B)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer_inf] at hN ⊢
  rw [inf_inf_inf_comm]; rw [inf_idem]
  exact le_trans (inf_le_inf hN B.le_normalizer) inf_normalizer_le_normalizer_inf

@[to_additive]
/--
Instance `normal_inf_normal` / 实例 `normal_inf_normal`

English:
instance normal_inf_normal
  signature: (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal]
  body: ⟨fun n hmem g => ⟨hH.conj_mem n hmem.1 g, hK.conj_mem n hmem.2 g⟩⟩

@[to_additive]

中文:
实例 normal_inf_normal
  签名: (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal]
  定义体: ⟨fun n hmem g => ⟨hH.conj_mem n hmem.1 g, hK.conj_mem n hmem.2 g⟩⟩

@[to_additive]

Depends on / 依赖: conj_mem, hH.conj_mem, hK.conj_mem
-/
instance normal_inf_normal (H K : Subgroup G) [hH : H.Normal] [hK : K.Normal] : (H ⊓ K).Normal :=
  ⟨fun n hmem g => ⟨hH.conj_mem n hmem.1 g, hK.conj_mem n hmem.2 g⟩⟩

@[to_additive]
/--
theorem `normal_iInf_normal` / 定理 `normal_iInf_normal`

English:
theorem normal_iInf_normal
  statement: {ι : Sort*} {a : ι -> Subgroup G}
  proof: by
  constructor
  intro g g_in_iInf h
  rw [Subgroup.mem_iInf] at g_in_iInf ⊢
  intro i
  exact (norm i).conj_mem g (g_in_iInf i) h

@[to_additive]

中文:
定理 normal_iInf_normal
  结论: {ι : Sort*} {a : ι -> Subgroup G}
  证明: by
  constructor
  intro g g_in_iInf h
  rw [Subgroup.mem_iInf] at g_in_iInf ⊢
  intro i
  exact (norm i).conj_mem g (g_in_iInf i) h

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.mem_iInf, conj_mem, g_in_iInf, mem_iInf
-/
theorem normal_iInf_normal {ι : Sort*} {a : ι -> Subgroup G}
    (norm : forall i : ι, (a i).Normal) : (iInf a).Normal := by
  constructor
  intro g g_in_iInf h
  rw [Subgroup.mem_iInf] at g_in_iInf ⊢
  intro i
  exact (norm i).conj_mem g (g_in_iInf i) h

@[to_additive]
/--
theorem `SubgroupNormal.mem_comm` / 定理 `SubgroupNormal.mem_comm`

English:
theorem SubgroupNormal.mem_comm
  statement: {H K : Subgroup G} (hK : H <= K) [hN : (H.subgroupOf K).Normal]
  proof: by
  have := (normal_subgroupOf_iff hK).mp hN (a * b) b h hb
  rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at this

中文:
定理 SubgroupNormal.mem_comm
  结论: {H K : Subgroup G} (hK : H <= K) [hN : (H.subgroupOf K).Normal]
  证明: by
  have := (normal_subgroupOf_iff hK).mp hN (a * b) b h hb
  rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at this

Depends on / 依赖: mul_assoc, mul_inv_cancel, mul_one, normal_subgroupOf_iff
-/
theorem SubgroupNormal.mem_comm {H K : Subgroup G} (hK : H <= K) [hN : (H.subgroupOf K).Normal]
    {a b : G} (hb : b in K) (h : a * b in H) : b * a in H := by
  have := (normal_subgroupOf_iff hK).mp hN (a * b) b h hb
  rwa [mul_assoc, mul_assoc, mul_inv_cancel, mul_one] at this

/-- Elements of disjoint, normal subgroups commute. -/
@[to_additive /-- Elements of disjoint, normal subgroups commute. -/]
/--
theorem `commute_of_normal_of_disjoint` / 定理 `commute_of_normal_of_disjoint`

English:
theorem commute_of_normal_of_disjoint
  statement: (H₁ H₂ : Subgroup G) (hH₁ : H₁.Normal) (hH₂ : H₂.Normal)
  proof: by
  suffices x * y * x⁻¹ * y⁻¹ = 1 by
    change x * y = y * x
    · rw [mul_assoc, mul_eq_one_iff_eq_inv] at this
      simpa
  apply hdis.le_bot
  constructor
  · suffices x * (y * x⁻¹ * y⁻¹) in H₁ by simpa [mul_assoc]
    exact H₁.mul_mem hx (hH₁.conj_mem _ (H₁.inv_mem hx) _)
  · change x * y * 

中文:
定理 commute_of_normal_of_disjoint
  结论: (H₁ H₂ : Subgroup G) (hH₁ : H₁.Normal) (hH₂ : H₂.Normal)
  证明: by
  suffices x * y * x⁻¹ * y⁻¹ = 1 by
    change x * y = y * x
    · rw [mul_assoc, mul_eq_one_iff_eq_inv] at this
      simpa
  apply hdis.le_bot
  constructor
  · suffices x * (y * x⁻¹ * y⁻¹) in H₁ by simpa [mul_assoc]
    exact H₁.mul_mem hx (hH₁.conj_mem _ (H₁.inv_mem hx) _)
  · change x * y * 

Depends on / 依赖: conj_mem, hdis.le_bot, inv_mem, le_bot, mul_assoc, mul_eq_one_iff_eq_inv, mul_mem
-/
theorem commute_of_normal_of_disjoint (H₁ H₂ : Subgroup G) (hH₁ : H₁.Normal) (hH₂ : H₂.Normal)
    (hdis : Disjoint H₁ H₂) (x y : G) (hx : x in H₁) (hy : y in H₂) : Commute x y := by
  suffices x * y * x⁻¹ * y⁻¹ = 1 by
    change x * y = y * x
    · rw [mul_assoc, mul_eq_one_iff_eq_inv] at this
      simpa
  apply hdis.le_bot
  constructor
  · suffices x * (y * x⁻¹ * y⁻¹) in H₁ by simpa [mul_assoc]
    exact H₁.mul_mem hx (hH₁.conj_mem _ (H₁.inv_mem hx) _)
  · change x * y * x⁻¹ * y⁻¹ in H₂
    apply H₂.mul_mem _ (H₂.inv_mem hy)
    apply hH₂.conj_mem _ hy

@[to_additive]
/--
theorem `normal_subgroupOf_of_le_normalizer` / 定理 `normal_subgroupOf_of_le_normalizer`

English:
theorem normal_subgroupOf_of_le_normalizer
  statement: {H N : Subgroup G}
  proof: by
  rw [normal_subgroupOf_iff_le_normalizer_inf]
  exact (le_inf hLE H.le_normalizer).trans inf_normalizer_le_normalizer_inf

@[to_additive]

中文:
定理 normal_subgroupOf_of_le_normalizer
  结论: {H N : Subgroup G}
  证明: by
  rw [normal_subgroupOf_iff_le_normalizer_inf]
  exact (le_inf hLE H.le_normalizer).trans inf_normalizer_le_normalizer_inf

@[to_additive]

Depends on / 依赖: H.le_normalizer, inf_normalizer_le_normalizer_inf, le_inf, le_normalizer, normal_subgroupOf_iff_le_normalizer_inf
-/
theorem normal_subgroupOf_of_le_normalizer {H N : Subgroup G}
    (hLE : H <= normalizer N) : (N.subgroupOf H).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer_inf]
  exact (le_inf hLE H.le_normalizer).trans inf_normalizer_le_normalizer_inf

@[to_additive]
/--
theorem `normal_subgroupOf_sup_of_le_normalizer` / 定理 `normal_subgroupOf_sup_of_le_normalizer`

English:
theorem normal_subgroupOf_sup_of_le_normalizer
  statement: {H N : Subgroup G}
  proof: by
  rw [normal_subgroupOf_iff_le_normalizer le_sup_right]
  exact sup_le hLE le_normalizer

中文:
定理 normal_subgroupOf_sup_of_le_normalizer
  结论: {H N : Subgroup G}
  证明: by
  rw [normal_subgroupOf_iff_le_normalizer le_sup_right]
  exact sup_le hLE le_normalizer

Depends on / 依赖: le_normalizer, le_sup_right, normal_subgroupOf_iff_le_normalizer, sup_le
-/
theorem normal_subgroupOf_sup_of_le_normalizer {H N : Subgroup G}
    (hLE : H <= normalizer N) : (N.subgroupOf (H ⊔ N)).Normal := by
  rw [normal_subgroupOf_iff_le_normalizer le_sup_right]
  exact sup_le hLE le_normalizer

end SubgroupNormal

@[to_additive]
/--
Instance `normal_subgroupOf_closure_normalizer` / 实例 `normal_subgroupOf_closure_normalizer`

English:
instance normal_subgroupOf_closure_normalizer
  signature: (s : Set G)
  body: normal_subgroupOf_of_le_normalizer normalizer_le_normalizer_closure s

中文:
实例 normal_subgroupOf_closure_normalizer
  签名: (s : Set G)
  定义体: normal_subgroupOf_of_le_normalizer normalizer_le_normalizer_closure s

Depends on / 依赖: normal_subgroupOf_of_le_normalizer, normalizer_le_normalizer_closure
-/
instance normal_subgroupOf_closure_normalizer (s : Set G) :
    (closure s |>.subgroupOf <| normalizer s).Normal :=
normal_subgroupOf_of_le_normalizer normalizer_le_normalizer_closure s

end Subgroup

namespace IsConj

open Subgroup

set_option backward.isDefEq.respectTransparency false in
/--
theorem `normalClosure_eq_top_of` / 定理 `normalClosure_eq_top_of`

English:
theorem normalClosure_eq_top_of
  statement: {N : Subgroup G} [hn : N.Normal] {g g' : G} {hg : g in N}
  proof: by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  have h : forall x : N, (MulAut.conj c) x in N := by
    rintro ⟨x, hx⟩
    exact hn.conj_mem _ hx c
  have hs : Function.Surjective (((MulAut.conj c).toMonoidHom.domRestrict N).codRestrict _ h) := by
    rintro ⟨x, hx⟩
    refine ⟨⟨c⁻¹ * x * c, ?_⟩, ?_⟩
    

中文:
定理 normalClosure_eq_top_of
  结论: {N : Subgroup G} [hn : N.Normal] {g g' : G} {hg : g in N}
  证明: by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  have h : forall x : N, (MulAut.conj c) x in N := by
    rintro ⟨x, hx⟩
    exact hn.conj_mem _ hx c
  have hs : Function.Surjective (((MulAut.conj c).toMonoidHom.domRestrict N).codRestrict _ h) := by
    rintro ⟨x, hx⟩
    refine ⟨⟨c⁻¹ * x * c, ?_⟩, ?_⟩
    

Depends on / 依赖: Function, Function.Surjective, MonoidHom, MonoidHom.codRestrict_apply, MonoidHom.domRestrict_apply, MulAut, MulAut.conj, MulAut.conj_apply, MulEquiv, MulEquiv.coe_toMonoidHom, Subtype, Subtype.mk_eq_mk, Surjective, codRestrict, codRestrict_apply, coe_toMonoidHom, conj_apply, conj_mem, domRestrict, domRestrict_apply
-/
theorem normalClosure_eq_top_of {N : Subgroup G} [hn : N.Normal] {g g' : G} {hg : g in N}
    {hg' : g' in N} (hc : IsConj g g') (ht : normalClosure ({⟨g, hg⟩} : Set N) = ⊤) :
    normalClosure ({⟨g', hg'⟩} : Set N) = ⊤ := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  have h : forall x : N, (MulAut.conj c) x in N := by
    rintro ⟨x, hx⟩
    exact hn.conj_mem _ hx c
  have hs : Function.Surjective (((MulAut.conj c).toMonoidHom.domRestrict N).codRestrict _ h) := by
    rintro ⟨x, hx⟩
    refine ⟨⟨c⁻¹ * x * c, ?_⟩, ?_⟩
    · have h := hn.conj_mem _ hx c⁻¹
      rwa [inv_inv] at h
    simp only [MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      MonoidHom.domRestrict_apply, Subtype.mk_eq_mk, ← mul_assoc, mul_inv_cancel, one_mul]
    rw [mul_assoc]; rw [mul_inv_cancel]; rw [mul_one]
  rw [eq_top_iff]; rw [← MonoidHom.range_eq_top.2 hs]; rw [MonoidHom.range_eq_map]
  grw [eq_top_iff.1 ht]
  refine map_le_iff_le_comap.2 (normalClosure_le_normal ?_)
  rw [Set.singleton_subset_iff]; rw [SetLike.mem_coe]
  simp only [MonoidHom.codRestrict_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    MonoidHom.domRestrict_apply, mem_comap]
  exact subset_normalClosure (Set.mem_singleton _)

end IsConj

namespace ConjClasses

/--
Definition of `noncenter` / `noncenter` 的定义

English:
definition noncenter
  signature: (G : Type*) [Monoid G]
  body: {x | x.carrier.Nontrivial}

中文:
定义 noncenter
  签名: (G : 类型) [Monoid G]
  定义体: {x | x.carrier.Nontrivial}

Depends on / 依赖: Nontrivial, carrier, x.carrier.Nontrivial
-/
def noncenter (G : Type*) [Monoid G] : Set (ConjClasses G) :=
  {x | x.carrier.Nontrivial}

/--
lemma `mem_noncenter` / 引理 `mem_noncenter`

English:
lemma mem_noncenter
  given: {G} [Monoid G] (g : ConjClasses G)
  proof: Iff.rfl

中文:
引理 mem_noncenter
  条件: {G} [Monoid G] (g : ConjClasses G)
  证明: Iff.rfl
-/
@[simp] lemma mem_noncenter {G} [Monoid G] (g : ConjClasses G) :
    g in noncenter G ↔ g.carrier.Nontrivial := Iff.rfl

end ConjClasses

namespace AddSubgroup

variable {M : Type*} [AddGroup M] (I : AddSubgroup M) (G : Type*)
    [Group G] [MulAction G M]

/--
Definition of `inertia` / `inertia` 的定义

English:
definition inertia
  signature: : Subgroup G where
  body: { σ | forall x, σ • x - x in I }
  mul_mem' {a b} ha hb x := by simpa [mul_smul] using add_mem (ha (b • x)) (hb x)
  one_mem' := by simp [zero_mem]
  inv_mem' {a} ha x := by simpa using sub_mem_comm_iff.mp (ha (a⁻¹ • x))

中文:
定义 inertia
  签名: : Subgroup G where
  定义体: { σ | forall x, σ • x - x in I }
  mul_mem' {a b} ha hb x := by simpa [mul_smul] using add_mem (ha (b • x)) (hb x)
  one_mem' := by simp [zero_mem]
  inv_mem' {a} ha x := by simpa using sub_mem_comm_iff.mp (ha (a⁻¹ • x))
-/
def inertia : Subgroup G where
  carrier := { σ | forall x, σ • x - x in I }
  mul_mem' {a b} ha hb x := by simpa [mul_smul] using add_mem (ha (b • x)) (hb x)
  one_mem' := by simp [zero_mem]
  inv_mem' {a} ha x := by simpa using sub_mem_comm_iff.mp (ha (a⁻¹ • x))

variable {I G} in
@[simp]
/--
lemma `mem_inertia` / 引理 `mem_inertia`

English:
lemma mem_inertia
  given: {σ : G}
  statement: σ in I.inertia G ↔ forall x, σ • x - x in I
  proof: .rfl

中文:
引理 mem_inertia
  条件: {σ : G}
  结论: σ in I.inertia G ↔ 对任意 x, σ • x - x in I
  证明: .rfl
-/
lemma mem_inertia {σ : G} : σ in I.inertia G ↔ forall x, σ • x - x in I := .rfl

variable {G} in
@[simp]
/--
lemma `subgroupOf_inertia` / 引理 `subgroupOf_inertia`

English:
lemma subgroupOf_inertia
  given: (H : Subgroup G)
  statement: (I.inertia G).subgroupOf H = I.inertia H
  proof: rfl

中文:
引理 subgroupOf_inertia
  条件: (H : Subgroup G)
  结论: (I.inertia G).subgroupOf H = I.inertia H
  证明: rfl
-/
lemma subgroupOf_inertia (H : Subgroup G) : (I.inertia G).subgroupOf H = I.inertia H :=
  rfl

variable {I G} in
/--
lemma `coe_mem_inertia` / 引理 `coe_mem_inertia`

English:
lemma coe_mem_inertia
  given: {H : Subgroup G} {σ : H}
  statement: ↑σ in I.inertia G ↔ σ in I.inertia H
  proof: .rfl

中文:
引理 coe_mem_inertia
  条件: {H : Subgroup G} {σ : H}
  结论: ↑σ in I.inertia G ↔ σ in I.inertia H
  证明: .rfl
-/
lemma coe_mem_inertia {H : Subgroup G} {σ : H} : ↑σ in I.inertia G ↔ σ in I.inertia H := .rfl

variable {G} in
@[simp]
/--
lemma `inertia_map_subtype` / 引理 `inertia_map_subtype`

English:
lemma inertia_map_subtype
  given: (H : Subgroup G)
  statement: (I.inertia H).map H.subtype = I.inertia G ⊓ H
  proof: by
  rw [← AddSubgroup.subgroupOf_inertia]; rw [Subgroup.subgroupOf_map_subtype]

中文:
引理 inertia_map_subtype
  条件: (H : Subgroup G)
  结论: (I.inertia H).map H.subtype = I.inertia G ⊓ H
  证明: by
  rw [← AddSubgroup.subgroupOf_inertia]; rw [Subgroup.subgroupOf_map_subtype]

Depends on / 依赖: AddSubgroup, AddSubgroup.subgroupOf_inertia, Subgroup, Subgroup.subgroupOf_map_subtype, subgroupOf_inertia, subgroupOf_map_subtype
-/
lemma inertia_map_subtype (H : Subgroup G) : (I.inertia H).map H.subtype = I.inertia G ⊓ H := by
  rw [← AddSubgroup.subgroupOf_inertia]; rw [Subgroup.subgroupOf_map_subtype]

end AddSubgroup
