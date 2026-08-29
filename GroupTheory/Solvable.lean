/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `derivedSeries G n` : the `n`th term in the derived series of `G`, defined by iterating
    `general_commutator` starting with the top subgroup
* `IsSolvable G` : the group `G` is solvable
-/

@[expose] public section

open Subgroup

open scoped commutatorElement

variable {G G' : Type*} [Group G] [Group G'] {f : G ->* G'}

section derivedSeries

variable (G)

/--
Definition of `derivedSeries` / `derivedSeries` 的定义

English:
definition derivedSeries
  signature: : Nat -> Subgroup G

中文:
定义 derivedSeries
  签名: : 自然数 -> 子群 G
-/
def derivedSeries : Nat -> Subgroup G
  | 0 => ⊤
  | n + 1 => ⁅derivedSeries n, derivedSeries n⁆

@[simp]
/--
theorem `derivedSeries_zero` / 定理 `derivedSeries_zero`

English:
theorem derivedSeries_zero
  statement: derivedSeries G 0 = ⊤
  proof: rfl

@[simp]

中文:
定理 derivedSeries_zero
  结论: derivedSeries G 0 = ⊤
  证明: rfl

@[simp]
-/
theorem derivedSeries_zero : derivedSeries G 0 = ⊤ :=
  rfl

@[simp]
/--
theorem `derivedSeries_succ` / 定理 `derivedSeries_succ`

English:
theorem derivedSeries_succ
  given: (n : Nat)
  proof: rfl

中文:
定理 derivedSeries_succ
  条件: (n : 自然数)
  证明: rfl
-/
theorem derivedSeries_succ (n : Nat) :
    derivedSeries G (n + 1) = ⁅derivedSeries G n, derivedSeries G n⁆ :=
  rfl

/--
theorem `derivedSeries_normal` / 定理 `derivedSeries_normal`

English:
theorem derivedSeries_normal
  given: (n : Nat)
  statement: (derivedSeries G n).Normal
  proof: by
  induction n with
  | zero => exact (⊤ : Subgroup G).normal_of_characteristic
  | succ n ih => exact Subgroup.commutator_normal (derivedSeries G n) (derivedSeries G n)

@[simp 1100]

中文:
定理 derivedSeries_normal
  条件: (n : 自然数)
  结论: (derivedSeries G n).正规
  证明: by
  induction n with
  | zero => exact (⊤ : Subgroup G).normal_of_characteristic
  | succ n ih => exact Subgroup.commutator_normal (derivedSeries G n) (derivedSeries G n)

@[simp 1100]

Depends on / 依赖: Subgroup, Subgroup.commutator_normal, commutator_normal, derivedSeries, normal_of_characteristic
-/
theorem derivedSeries_normal (n : Nat) : (derivedSeries G n).Normal := by
  induction n with
  | zero => exact (⊤ : Subgroup G).normal_of_characteristic
  | succ n ih => exact Subgroup.commutator_normal (derivedSeries G n) (derivedSeries G n)

@[simp 1100]
/--
theorem `derivedSeries_one` / 定理 `derivedSeries_one`

English:
theorem derivedSeries_one
  statement: derivedSeries G 1 = commutator G
  proof: rfl

中文:
定理 derivedSeries_one
  结论: derivedSeries G 1 = commutator G
  证明: rfl
-/
theorem derivedSeries_one : derivedSeries G 1 = commutator G :=
  rfl

/--
theorem `derivedSeries_antitone` / 定理 `derivedSeries_antitone`

English:
theorem derivedSeries_antitone
  statement: Antitone (derivedSeries G)
  proof: antitone_nat_of_succ_le fun n => (derivedSeries G n).commutator_le_self

中文:
定理 derivedSeries_antitone
  结论: 递减 (derivedSeries G)
  证明: antitone_nat_of_succ_le fun n => (derivedSeries G n).commutator_le_self

Depends on / 依赖: antitone_nat_of_succ_le, commutator_le_self, derivedSeries
-/
theorem derivedSeries_antitone : Antitone (derivedSeries G) :=
  antitone_nat_of_succ_le fun n => (derivedSeries G n).commutator_le_self

/--
Instance `derivedSeries_characteristic` / 实例 `derivedSeries_characteristic`

English:
instance derivedSeries_characteristic
  signature: (n : Nat)
  body: by
  induction n with
  | zero => exact Subgroup.topCharacteristic
  | succ n _ => exact Subgroup.commutator_characteristic _ _

中文:
实例 derivedSeries_characteristic
  签名: (n : 自然数)
  定义体: by
  induction n with
  | zero => exact Subgroup.topCharacteristic
  | succ n _ => exact Subgroup.commutator_characteristic _ _

Depends on / 依赖: Subgroup, Subgroup.commutator_characteristic, Subgroup.topCharacteristic, commutator_characteristic, topCharacteristic
-/
instance derivedSeries_characteristic (n : Nat) : (derivedSeries G n).Characteristic := by
  induction n with
  | zero => exact Subgroup.topCharacteristic
  | succ n _ => exact Subgroup.commutator_characteristic _ _

end derivedSeries

section CommutatorMap

section DerivedSeriesMap

variable (f) in
/--
theorem `map_derivedSeries_le_derivedSeries` / 定理 `map_derivedSeries_le_derivedSeries`

English:
theorem map_derivedSeries_le_derivedSeries
  given: (n : Nat)
  proof: by
  induction n with
  | zero => exact le_top
  | succ n ih => simp only [derivedSeries_succ, map_commutator, commutator_mono, ih]

中文:
定理 map_derivedSeries_le_derivedSeries
  条件: (n : 自然数)
  证明: by
  induction n with
  | zero => exact le_top
  | succ n ih => simp only [derivedSeries_succ, map_commutator, commutator_mono, ih]

Depends on / 依赖: commutator_mono, derivedSeries_succ, le_top, map_commutator
-/
theorem map_derivedSeries_le_derivedSeries (n : Nat) :
    (derivedSeries G n).map f <= derivedSeries G' n := by
  induction n with
  | zero => exact le_top
  | succ n ih => simp only [derivedSeries_succ, map_commutator, commutator_mono, ih]

/--
theorem `derivedSeries_le_map_derivedSeries` / 定理 `derivedSeries_le_map_derivedSeries`

English:
theorem derivedSeries_le_map_derivedSeries
  given: (hf : Function.Surjective f) (n : Nat)
  proof: by
  induction n with
  | zero => exact (map_top_of_surjective f hf).ge
  | succ n ih => exact commutator_le_map_commutator ih ih

中文:
定理 derivedSeries_le_map_derivedSeries
  条件: (hf : 函数.满射 f) (n : 自然数)
  证明: by
  induction n with
  | zero => exact (map_top_of_surjective f hf).ge
  | succ n ih => exact commutator_le_map_commutator ih ih

Depends on / 依赖: commutator_le_map_commutator, map_top_of_surjective
-/
theorem derivedSeries_le_map_derivedSeries (hf : Function.Surjective f) (n : Nat) :
    derivedSeries G' n <= (derivedSeries G n).map f := by
  induction n with
  | zero => exact (map_top_of_surjective f hf).ge
  | succ n ih => exact commutator_le_map_commutator ih ih

/--
theorem `map_derivedSeries_eq` / 定理 `map_derivedSeries_eq`

English:
theorem map_derivedSeries_eq
  given: (hf : Function.Surjective f) (n : Nat)
  proof: le_antisymm (map_derivedSeries_le_derivedSeries f n) (derivedSeries_le_map_derivedSeries hf n)

中文:
定理 map_derivedSeries_eq
  条件: (hf : 函数.满射 f) (n : 自然数)
  证明: le_antisymm (map_derivedSeries_le_derivedSeries f n) (derivedSeries_le_map_derivedSeries hf n)

Depends on / 依赖: derivedSeries_le_map_derivedSeries, le_antisymm, map_derivedSeries_le_derivedSeries
-/
theorem map_derivedSeries_eq (hf : Function.Surjective f) (n : Nat) :
    (derivedSeries G n).map f = derivedSeries G' n :=
  le_antisymm (map_derivedSeries_le_derivedSeries f n) (derivedSeries_le_map_derivedSeries hf n)

end DerivedSeriesMap

end CommutatorMap

section Solvable

variable (G)

namespace Group

/-- A group `G` is solvable if its derived series is eventually trivial. We use this definition
  because it's the most convenient one to work with. -/
@[mk_iff isSolvable_def, wikidata Q759832]
/--
Definition of `IsSolvable` / `IsSolvable` 的定义

English:
class IsSolvable
  parameters: : Prop where
  axioms and operations (1):
    - solvable : exists n : Nat, derivedSeries G n = ⊥

中文:
类 是可解
  参数: : 命题 where
  公理与运算 (1 个):
    - solvable : 存在 n : 自然数, derivedSeries G n = ⊥
-/
class IsSolvable : Prop where
  /-- A group `G` is solvable if its derived series is eventually trivial. -/
  solvable : exists n : Nat, derivedSeries G n = ⊥

@[deprecated (since := "2026-07-16")]
alias _root_.IsSolvable := Group.IsSolvable

@[deprecated (since := "2026-07-17")]
alias _root_.isSolvable_def := Group.isSolvable_def

instance (priority := 100) {G : Type*} [CommGroup G] : IsSolvable G :=
  ⟨⟨1, le_bot_iff.mp (Abelianization.commutator_subset_ker (MonoidHom.id G))⟩⟩

/--
theorem `isSolvable_of_comm` / 定理 `isSolvable_of_comm`

English:
theorem isSolvable_of_comm
  given: {G : Type*} [hG : Group G] (h : forall a b : G, a * b = b * a)
  proof: by
  let hG' : CommGroup G := { hG with mul_comm := h }
  cases hG
  infer_instance

@[deprecated (since := "2026-07-16")]
alias _root_.isSolvable_of_comm := Group.isSolvable_of_comm

中文:
定理 isSolvable_of_comm
  条件: {G : 类型} [hG : 群 G] (h : 对任意 a b : G, a * b = b * a)
  证明: by
  let hG' : CommGroup G := { hG with mul_comm := h }
  cases hG
  infer_instance

@[deprecated (since := "2026-07-16")]
alias _root_.isSolvable_of_comm := Group.isSolvable_of_comm

Depends on / 依赖: CommGroup, infer_instance, mul_comm
-/
theorem isSolvable_of_comm {G : Type*} [hG : Group G] (h : forall a b : G, a * b = b * a) :
    IsSolvable G := by
  let hG' : CommGroup G := { hG with mul_comm := h }
  cases hG
  infer_instance

@[deprecated (since := "2026-07-16")]
alias _root_.isSolvable_of_comm := Group.isSolvable_of_comm

/--
theorem `isSolvable_of_top_eq_bot` / 定理 `isSolvable_of_top_eq_bot`

English:
theorem isSolvable_of_top_eq_bot
  given: (h : (⊤ : Subgroup G) = ⊥)
  statement: IsSolvable G
  proof: ⟨⟨0, h⟩⟩

@[deprecated (since := "2026-07-16")]
alias _root_.isSolvable_of_top_eq_bot := Group.isSolvable_of_top_eq_bot

中文:
定理 isSolvable_of_top_eq_bot
  条件: (h : (⊤ : 子群 G) = ⊥)
  结论: 是可解 G
  证明: ⟨⟨0, h⟩⟩

@[deprecated (since := "2026-07-16")]
alias _root_.isSolvable_of_top_eq_bot := Group.isSolvable_of_top_eq_bot
-/
theorem isSolvable_of_top_eq_bot (h : (⊤ : Subgroup G) = ⊥) : IsSolvable G :=
  ⟨⟨0, h⟩⟩

@[deprecated (since := "2026-07-16")]
alias _root_.isSolvable_of_top_eq_bot := Group.isSolvable_of_top_eq_bot

instance (priority := 100) [Subsingleton G] : IsSolvable G :=
  isSolvable_of_top_eq_bot G (by simp [eq_iff_true_of_subsingleton])

variable {G}

/--
theorem `isSolvable_of_ker_le_range` / 定理 `isSolvable_of_ker_le_range`

English:
theorem isSolvable_of_ker_le_range
  statement: {G' G'' : Type*} [Group G'] [Group G''] (f : G' ->* G)
  proof: by
  obtain ⟨n, hn⟩ := id hG''
  obtain ⟨m, hm⟩ := id hG'
  refine ⟨⟨n + m, le_bot_iff.mp (Subgroup.map_bot f ▸ hm ▸ ?_)⟩⟩
  clear hm
  induction m with
  | zero =>
    exact f.range_eq_map ▸ ((derivedSeries G n).map_eq_bot_iff.mp
      (le_bot_iff.mp ((map_derivedSeries_le_derivedSeries g n).trans 

中文:
定理 isSolvable_of_ker_le_range
  结论: {G' G'' : 类型} [群 G'] [群 G''] (f : G' ->* G)
  证明: by
  obtain ⟨n, hn⟩ := id hG''
  obtain ⟨m, hm⟩ := id hG'
  refine ⟨⟨n + m, le_bot_iff.mp (Subgroup.map_bot f ▸ hm ▸ ?_)⟩⟩
  clear hm
  induction m with
  | zero =>
    exact f.range_eq_map ▸ ((derivedSeries G n).map_eq_bot_iff.mp
      (le_bot_iff.mp ((map_derivedSeries_le_derivedSeries g n).trans 

Depends on / 依赖: Subgroup, Subgroup.map_bot, commutator_le_map_commutator, derivedSeries, f.range_eq_map, hn.le, le_bot_iff, le_bot_iff.mp, map_bot, map_derivedSeries_le_derivedSeries, map_eq_bot_iff, map_eq_bot_iff.mp, range_eq_map
-/
theorem isSolvable_of_ker_le_range {G' G'' : Type*} [Group G'] [Group G''] (f : G' ->* G)
    (g : G ->* G'') (hfg : g.ker <= f.range) [hG' : IsSolvable G'] [hG'' : IsSolvable G''] :
    IsSolvable G := by
  obtain ⟨n, hn⟩ := id hG''
  obtain ⟨m, hm⟩ := id hG'
  refine ⟨⟨n + m, le_bot_iff.mp (Subgroup.map_bot f ▸ hm ▸ ?_)⟩⟩
  clear hm
  induction m with
  | zero =>
    exact f.range_eq_map ▸ ((derivedSeries G n).map_eq_bot_iff.mp
      (le_bot_iff.mp ((map_derivedSeries_le_derivedSeries g n).trans hn.le))).trans hfg
  | succ m hm => exact commutator_le_map_commutator hm hm

@[deprecated (since := "2026-07-16")]
alias _root_.solvable_of_ker_le_range := isSolvable_of_ker_le_range

/--
theorem `isSolvable_of_isSolvable_injective` / 定理 `isSolvable_of_isSolvable_injective`

English:
theorem isSolvable_of_isSolvable_injective
  given: (hf : Function.Injective f) [IsSolvable G']
  proof: isSolvable_of_ker_le_range (1 : G' ->* G) f ((f.ker_eq_bot hf).symm ▸ bot_le)

@[deprecated (since := "2026-07-16")]
alias _root_.solvable_of_solvable_injective := isSolvable_of_isSolvable_injective

中文:
定理 isSolvable_of_isSolvable_injective
  条件: (hf : 函数.单射 f) [是可解 G']
  证明: isSolvable_of_ker_le_range (1 : G' ->* G) f ((f.ker_eq_bot hf).symm ▸ bot_le)

@[deprecated (since := "2026-07-16")]
alias _root_.solvable_of_solvable_injective := isSolvable_of_isSolvable_injective

Depends on / 依赖: bot_le, f.ker_eq_bot, isSolvable_of_ker_le_range, ker_eq_bot
-/
theorem isSolvable_of_isSolvable_injective (hf : Function.Injective f) [IsSolvable G'] :
    IsSolvable G :=
  isSolvable_of_ker_le_range (1 : G' ->* G) f ((f.ker_eq_bot hf).symm ▸ bot_le)

@[deprecated (since := "2026-07-16")]
alias _root_.solvable_of_solvable_injective := isSolvable_of_isSolvable_injective

instance (H : Subgroup G) [IsSolvable G] : IsSolvable H :=
  isSolvable_of_isSolvable_injective H.subtype_injective

/--
theorem `isSolvable_of_surjective` / 定理 `isSolvable_of_surjective`

English:
theorem isSolvable_of_surjective
  given: (hf : Function.Surjective f) [IsSolvable G]
  statement: IsSolvable G'
  proof: isSolvable_of_ker_le_range f (1 : G' ->* G) (f.range_eq_top_of_surjective hf ▸ le_top)

@[deprecated (since := "2026-07-16")]
alias _root_.solvable_of_surjective := isSolvable_of_surjective

中文:
定理 isSolvable_of_surjective
  条件: (hf : 函数.满射 f) [是可解 G]
  结论: 是可解 G'
  证明: isSolvable_of_ker_le_range f (1 : G' ->* G) (f.range_eq_top_of_surjective hf ▸ le_top)

@[deprecated (since := "2026-07-16")]
alias _root_.solvable_of_surjective := isSolvable_of_surjective

Depends on / 依赖: f.range_eq_top_of_surjective, isSolvable_of_ker_le_range, le_top, range_eq_top_of_surjective
-/
theorem isSolvable_of_surjective (hf : Function.Surjective f) [IsSolvable G] : IsSolvable G' :=
  isSolvable_of_ker_le_range f (1 : G' ->* G) (f.range_eq_top_of_surjective hf ▸ le_top)

@[deprecated (since := "2026-07-16")]
alias _root_.solvable_of_surjective := isSolvable_of_surjective

instance (H : Subgroup G) [H.Normal] [IsSolvable G] :
    IsSolvable (G ⧸ H) :=
  isSolvable_of_surjective (QuotientGroup.mk'_surjective H)

/--
theorem `isSolvable_iff_subgroup_quotient` / 定理 `isSolvable_iff_subgroup_quotient`

English:
theorem isSolvable_iff_subgroup_quotient
  given: (H : Subgroup G) [H.Normal]
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isSolvable_of_ker_le_range H.subtype (QuotientGroup.mk' H) (by simp)⟩

中文:
定理 isSolvable_iff_subgroup_quotient
  条件: (H : 子群 G) [H.正规]
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isSolvable_of_ker_le_range H.subtype (QuotientGroup.mk' H) (by simp)⟩

Depends on / 依赖: H.subtype, QuotientGroup, QuotientGroup.mk, isSolvable_of_ker_le_range, subtype
-/
theorem isSolvable_iff_subgroup_quotient (H : Subgroup G) [H.Normal] :
    IsSolvable G ↔ IsSolvable H ∧ IsSolvable (G ⧸ H) :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isSolvable_of_ker_le_range H.subtype (QuotientGroup.mk' H) (by simp)⟩

instance {G' : Type*} [Group G'] [IsSolvable G] [IsSolvable G'] :
    IsSolvable (G × G') :=
  isSolvable_of_ker_le_range (MonoidHom.inl G G') (MonoidHom.snd G G') fun x hx =>
    ⟨x.1, Prod.ext rfl hx.symm⟩

variable (G) in
/--
theorem `IsSolvable.commutator_lt_top_of_nontrivial` / 定理 `IsSolvable.commutator_lt_top_of_nontrivial`

English:
theorem IsSolvable.commutator_lt_top_of_nontrivial
  given: [hG : IsSolvable G] [Nontrivial G]
  proof: by
  rw [lt_top_iff_ne_top]
  obtain ⟨n, hn⟩ := hG
  contrapose! hn
  refine ne_of_eq_of_ne ?_ top_ne_bot
  induction n with
  | zero => exact derivedSeries_zero G
  | succ n h => rwa [derivedSeries_succ, h]

@[deprecated (since := "2026-07-16")]
alias _root_.IsSolvable.commutator_lt_top_of_nontrivi

中文:
定理 是可解.commutator_lt_top_of_nontrivial
  条件: [hG : 是可解 G] [非平凡 G]
  证明: by
  rw [lt_top_iff_ne_top]
  obtain ⟨n, hn⟩ := hG
  contrapose! hn
  refine ne_of_eq_of_ne ?_ top_ne_bot
  induction n with
  | zero => exact derivedSeries_zero G
  | succ n h => rwa [derivedSeries_succ, h]

@[deprecated (since := "2026-07-16")]
alias _root_.IsSolvable.commutator_lt_top_of_nontrivi

Depends on / 依赖: contrapose, derivedSeries_succ, derivedSeries_zero, lt_top_iff_ne_top, ne_of_eq_of_ne, top_ne_bot
-/
theorem IsSolvable.commutator_lt_top_of_nontrivial [hG : IsSolvable G] [Nontrivial G] :
    commutator G < ⊤ := by
  rw [lt_top_iff_ne_top]
  obtain ⟨n, hn⟩ := hG
  contrapose! hn
  refine ne_of_eq_of_ne ?_ top_ne_bot
  induction n with
  | zero => exact derivedSeries_zero G
  | succ n h => rwa [derivedSeries_succ, h]

@[deprecated (since := "2026-07-16")]
alias _root_.IsSolvable.commutator_lt_top_of_nontrivial :=
  Group.IsSolvable.commutator_lt_top_of_nontrivial

/--
theorem `IsSolvable.commutator_lt_of_ne_bot` / 定理 `IsSolvable.commutator_lt_of_ne_bot`

English:
theorem IsSolvable.commutator_lt_of_ne_bot
  given: [IsSolvable G] {H : Subgroup G} (hH : H != ⊥)
  proof: by
  rw [← nontrivial_iff_ne_bot] at hH
  rw [← H.range_subtype]; rw [MonoidHom.range_eq_map]; rw [← map_commutator]; rw [map_subtype_lt_map_subtype]
  exact commutator_lt_top_of_nontrivial H

@[deprecated (since := "2026-07-16")]
alias _root_.IsSolvable.commutator_lt_of_ne_bot := Group.IsSolvable.c

中文:
定理 是可解.commutator_lt_of_ne_bot
  条件: [是可解 G] {H : 子群 G} (hH : H != ⊥)
  证明: by
  rw [← nontrivial_iff_ne_bot] at hH
  rw [← H.range_subtype]; rw [MonoidHom.range_eq_map]; rw [← map_commutator]; rw [map_subtype_lt_map_subtype]
  exact commutator_lt_top_of_nontrivial H

@[deprecated (since := "2026-07-16")]
alias _root_.IsSolvable.commutator_lt_of_ne_bot := Group.IsSolvable.c

Depends on / 依赖: H.range_subtype, MonoidHom, MonoidHom.range_eq_map, commutator_lt_top_of_nontrivial, map_commutator, map_subtype_lt_map_subtype, nontrivial_iff_ne_bot, range_eq_map, range_subtype
-/
theorem IsSolvable.commutator_lt_of_ne_bot [IsSolvable G] {H : Subgroup G} (hH : H != ⊥) :
    ⁅H, H⁆ < H := by
  rw [← nontrivial_iff_ne_bot] at hH
  rw [← H.range_subtype]; rw [MonoidHom.range_eq_map]; rw [← map_commutator]; rw [map_subtype_lt_map_subtype]
  exact commutator_lt_top_of_nontrivial H

@[deprecated (since := "2026-07-16")]
alias _root_.IsSolvable.commutator_lt_of_ne_bot := Group.IsSolvable.commutator_lt_of_ne_bot

/--
theorem `isSolvable_iff_commutator_lt` / 定理 `isSolvable_iff_commutator_lt`

English:
theorem isSolvable_iff_commutator_lt
  given: [WellFoundedLT (Subgroup G)]
  proof: by
  refine ⟨fun _ _ => IsSolvable.commutator_lt_of_ne_bot, fun h => ?_⟩
  suffices h : IsSolvable (⊤ : Subgroup G) from
    isSolvable_of_surjective (MonoidHom.range_eq_top.mp (range_subtype ⊤))
  induction (⊤ : Subgroup G) using WellFoundedLT.induction with | ind H hH
  rcases eq_or_ne H ⊥ with rf

中文:
定理 isSolvable_iff_commutator_lt
  条件: [WellFoundedLT (子群 G)]
  证明: by
  refine ⟨fun _ _ => IsSolvable.commutator_lt_of_ne_bot, fun h => ?_⟩
  suffices h : IsSolvable (⊤ : Subgroup G) from
    isSolvable_of_surjective (MonoidHom.range_eq_top.mp (range_subtype ⊤))
  induction (⊤ : Subgroup G) using WellFoundedLT.induction with | ind H hH
  rcases eq_or_ne H ⊥ with rf

Depends on / 依赖: IsSolvable, IsSolvable.commutator_lt_of_ne_bot, MonoidHom, MonoidHom.range_eq_top.mp, Subgroup, Subgroup.map_bot, WellFoundedLT, WellFoundedLT.induction, commutator_lt_of_ne_bot, derivedSer, derivedSeries_succ, eq_or_ne, infer_instance, isSolvable_of_surjective, map_bot, map_subtype_inj, range_eq_top, range_subtype
-/
theorem isSolvable_iff_commutator_lt [WellFoundedLT (Subgroup G)] :
    IsSolvable G ↔ forall H : Subgroup G, H != ⊥ -> ⁅H, H⁆ < H := by
  refine ⟨fun _ _ => IsSolvable.commutator_lt_of_ne_bot, fun h => ?_⟩
  suffices h : IsSolvable (⊤ : Subgroup G) from
    isSolvable_of_surjective (MonoidHom.range_eq_top.mp (range_subtype ⊤))
  induction (⊤ : Subgroup G) using WellFoundedLT.induction with | ind H hH
  rcases eq_or_ne H ⊥ with rfl | h'
  · infer_instance
  · obtain ⟨n, hn⟩ := hH ⁅H, H⁆ (h H h')
    use n + 1
    rw [← map_subtype_inj]; rw [Subgroup.map_bot] at hn ⊢
    rw [← hn]
    clear hn
    induction n with
    | zero =>
      rw [derivedSeries_succ]; rw [derivedSeries_zero]; rw [derivedSeries_zero]; rw [map_commutator]; rw [← MonoidHom.range_eq_map]; rw [← MonoidHom.range_eq_map]; rw [range_subtype]; rw [range_subtype]
    | succ n ih => rw [derivedSeries_succ, map_commutator, ih, derivedSeries_succ, map_commutator]

@[deprecated (since := "2026-07-16")]
alias _root_.isSolvable_iff_commutator_lt := Group.isSolvable_iff_commutator_lt

end Group

end Solvable

section IsSimpleGroup

variable [IsSimpleGroup G]

/--
theorem `IsSimpleGroup.derivedSeries_succ` / 定理 `IsSimpleGroup.derivedSeries_succ`

English:
theorem IsSimpleGroup.derivedSeries_succ
  given: {n : Nat}
  statement: derivedSeries G n.succ = commutator G
  proof: by
  induction n with
  | zero => exact derivedSeries_one G
  | succ n ih =>
    rw [_root_.derivedSeries_succ]; rw [ih]; rw [_root_.commutator]
    rcases (commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with h | h
    · rw [h, commutator_bot_left]
    · rwa [h]

中文:
定理 是单群.derivedSeries_succ
  条件: {n : 自然数}
  结论: derivedSeries G n.succ = commutator G
  证明: by
  induction n with
  | zero => exact derivedSeries_one G
  | succ n ih =>
    rw [_root_.derivedSeries_succ]; rw [ih]; rw [_root_.commutator]
    rcases (commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with h | h
    · rw [h, commutator_bot_left]
    · rwa [h]

Depends on / 依赖: Subgroup, _root_, _root_.commutator, _root_.derivedSeries_succ, commutator, commutator_bot_left, commutator_normal, derivedSeries_one, derivedSeries_succ, eq_bot_or_eq_top
-/
theorem IsSimpleGroup.derivedSeries_succ {n : Nat} : derivedSeries G n.succ = commutator G := by
  induction n with
  | zero => exact derivedSeries_one G
  | succ n ih =>
    rw [_root_.derivedSeries_succ]; rw [ih]; rw [_root_.commutator]
    rcases (commutator_normal (⊤ : Subgroup G) (⊤ : Subgroup G)).eq_bot_or_eq_top with h | h
    · rw [h, commutator_bot_left]
    · rwa [h]

/--
theorem `IsSimpleGroup.comm_iff_isSolvable` / 定理 `IsSimpleGroup.comm_iff_isSolvable`

English:
theorem IsSimpleGroup.comm_iff_isSolvable
  statement: (forall a b : G, a * b = b * a) ↔ Group.IsSolvable G
  proof: ⟨Group.isSolvable_of_comm, fun ⟨⟨n, hn⟩⟩ => by
    cases n
    · intro a b
      refine (mem_bot.1 ?_).trans (mem_bot.1 ?_).symm <;>
        · rw [← hn]
          exact mem_top _
    · rw [IsSimpleGroup.derivedSeries_succ] at hn
      intro a b
      rw [← mul_inv_eq_one]; rw [mul_inv_rev]; rw [← mu

中文:
定理 是单群.comm_iff_isSolvable
  结论: (对任意 a b : G, a * b = b * a) ↔ 群.是可解 G
  证明: ⟨Group.isSolvable_of_comm, fun ⟨⟨n, hn⟩⟩ => by
    cases n
    · intro a b
      refine (mem_bot.1 ?_).trans (mem_bot.1 ?_).symm <;>
        · rw [← hn]
          exact mem_top _
    · rw [IsSimpleGroup.derivedSeries_succ] at hn
      intro a b
      rw [← mul_inv_eq_one]; rw [mul_inv_rev]; rw [← mu

Depends on / 依赖: Group.isSolvable_of_comm, IsSimpleGroup, IsSimpleGroup.derivedSeries_succ, commutator_eq_closure, derivedSeries_succ, isSolvable_of_comm, mem_bot, mem_top, mul_assoc, mul_inv_eq_one, mul_inv_rev, subset_closure
-/
theorem IsSimpleGroup.comm_iff_isSolvable : (forall a b : G, a * b = b * a) ↔ Group.IsSolvable G :=
  ⟨Group.isSolvable_of_comm, fun ⟨⟨n, hn⟩⟩ => by
    cases n
    · intro a b
      refine (mem_bot.1 ?_).trans (mem_bot.1 ?_).symm <;>
        · rw [← hn]
          exact mem_top _
    · rw [IsSimpleGroup.derivedSeries_succ] at hn
      intro a b
      rw [← mul_inv_eq_one]; rw [mul_inv_rev]; rw [← mul_assoc]; rw [← mem_bot]; rw [← hn]; rw [commutator_eq_closure]
      exact subset_closure ⟨a, b, rfl⟩⟩

end IsSimpleGroup

section PermNotSolvable

/--
theorem `not_isSolvable_of_mem_derivedSeries` / 定理 `not_isSolvable_of_mem_derivedSeries`

English:
theorem not_isSolvable_of_mem_derivedSeries
  statement: {g : G} (h1 : g != 1)
  proof: mt (Group.isSolvable_def _).mp
    (not_exists_of_forall_not fun n h =>
      h1 (Subgroup.mem_bot.mp ((congr_arg (g in ·) h).mp (h2 n))))

@[deprecated (since := "2026-07-16")]
alias not_solvable_of_mem_derivedSeries := not_isSolvable_of_mem_derivedSeries

中文:
定理 not_isSolvable_of_mem_derivedSeries
  结论: {g : G} (h1 : g != 1)
  证明: mt (Group.isSolvable_def _).mp
    (not_exists_of_forall_not fun n h =>
      h1 (Subgroup.mem_bot.mp ((congr_arg (g in ·) h).mp (h2 n))))

@[deprecated (since := "2026-07-16")]
alias not_solvable_of_mem_derivedSeries := not_isSolvable_of_mem_derivedSeries

Depends on / 依赖: Group.isSolvable_def, Subgroup, Subgroup.mem_bot.mp, congr_arg, isSolvable_def, mem_bot, not_exists_of_forall_not
-/
theorem not_isSolvable_of_mem_derivedSeries {g : G} (h1 : g != 1)
    (h2 : forall n : Nat, g in derivedSeries G n) : ¬Group.IsSolvable G :=
  mt (Group.isSolvable_def _).mp
    (not_exists_of_forall_not fun n h =>
      h1 (Subgroup.mem_bot.mp ((congr_arg (g in ·) h).mp (h2 n))))

@[deprecated (since := "2026-07-16")]
alias not_solvable_of_mem_derivedSeries := not_isSolvable_of_mem_derivedSeries

/--
theorem `Equiv.Perm.not_isSolvable_fin_5` / 定理 `Equiv.Perm.not_isSolvable_fin_5`

English:
theorem Equiv.Perm.not_isSolvable_fin_5
  statement: ¬Group.IsSolvable (Equiv.Perm (Fin 5))
  proof: by
  let x : Equiv.Perm (Fin 5) := ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩
  let y : Equiv.Perm (Fin 5) := ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩
  let z : Equiv.Perm (Fin 5) := ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], by decide, by decide⟩
  have key : x = z * ⁅x,

中文:
定理 等价.置换.not_isSolvable_fin_5
  结论: ¬群.是可解 (等价.置换 (有限集 5))
  证明: by
  let x : Equiv.Perm (Fin 5) := ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩
  let y : Equiv.Perm (Fin 5) := ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩
  let z : Equiv.Perm (Fin 5) := ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], by decide, by decide⟩
  have key : x = z * ⁅x,

Depends on / 依赖: Equiv.Perm, derivedSe, mem_top, not_isSolvable_of_mem_derivedSeries
-/
theorem Equiv.Perm.not_isSolvable_fin_5 : ¬Group.IsSolvable (Equiv.Perm (Fin 5)) := by
  let x : Equiv.Perm (Fin 5) := ⟨![1, 2, 0, 3, 4], ![2, 0, 1, 3, 4], by decide, by decide⟩
  let y : Equiv.Perm (Fin 5) := ⟨![3, 4, 2, 0, 1], ![3, 4, 2, 0, 1], by decide, by decide⟩
  let z : Equiv.Perm (Fin 5) := ⟨![0, 3, 2, 1, 4], ![0, 3, 2, 1, 4], by decide, by decide⟩
  have key : x = z * ⁅x, y * x * y⁻¹⁆ * z⁻¹ := by unfold x y z; decide
  refine not_isSolvable_of_mem_derivedSeries (show x != 1 by decide) fun n => ?_
  induction n with
  | zero => exact mem_top x
  | succ n ih =>
    rw [key]; rw [(derivedSeries_normal _ _).mem_comm_iff]; rw [inv_mul_cancel_left]
    exact commutator_mem_commutator ih ((derivedSeries_normal _ _).conj_mem _ ih _)

@[deprecated (since := "2026-07-16")]
alias Equiv.Perm.fin_5_not_solvable := Equiv.Perm.not_isSolvable_fin_5

/--
theorem `Equiv.Perm.not_isSolvable` / 定理 `Equiv.Perm.not_isSolvable`

English:
theorem Equiv.Perm.not_isSolvable
  given: (X : Type*) (hX : 5 <= Cardinal.mk X)
  proof: by
  intro h
  have key : Nonempty (Fin 5 ↪ X) := by
    rwa [← Cardinal.lift_mk_le, Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_id]
  exact
    Equiv.Perm.not_isSolvable_fin_5 (Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Nonempty.some key)))

@[de

中文:
定理 等价.置换.not_isSolvable
  条件: (X : 类型) (hX : 5 <= 基数.mk X)
  证明: by
  intro h
  have key : Nonempty (Fin 5 ↪ X) := by
    rwa [← Cardinal.lift_mk_le, Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_id]
  exact
    Equiv.Perm.not_isSolvable_fin_5 (Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Nonempty.some key)))

@[de

Depends on / 依赖: Cardinal, Cardinal.lift_id, Cardinal.lift_mk_le, Cardinal.lift_natCast, Cardinal.mk_fin, Equiv.Perm.not_isSolvable_fin_5, Equiv.Perm.viaEmbeddingHom_injective, Group.isSolvable_of_isSolvable_injective, Nonempty, Nonempty.some, isSolvable_of_isSolvable_injective, lift_id, lift_mk_le, lift_natCast, mk_fin, not_isSolvable_fin_5, viaEmbeddingHom_injective
-/
theorem Equiv.Perm.not_isSolvable (X : Type*) (hX : 5 <= Cardinal.mk X) :
    ¬Group.IsSolvable (Equiv.Perm X) := by
  intro h
  have key : Nonempty (Fin 5 ↪ X) := by
    rwa [← Cardinal.lift_mk_le, Cardinal.mk_fin, Cardinal.lift_natCast, Cardinal.lift_id]
  exact
    Equiv.Perm.not_isSolvable_fin_5 (Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Nonempty.some key)))

@[deprecated (since := "2026-07-16")]
alias Equiv.Perm.not_solvable := Equiv.Perm.not_isSolvable

end PermNotSolvable
