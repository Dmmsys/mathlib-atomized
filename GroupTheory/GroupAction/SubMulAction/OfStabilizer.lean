/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Embedding
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fin.Tuple.Embedding

/-! # The SubMulAction of the stabilizer of a point on the complement of that point

When a group `G` acts on a type `α`, the stabilizer of a point `a : α`
acts naturally on the complement of that point.

Such actions
(as the similar one, `SubMulAction.ofFixingSubgroup`,
for the fixing subgroup of a set acting on the complement of that set)
are useful to study the multiple transitivity of the group `G`,
since `n`-transitivity of `G` on `α` is equivalent to `n - 1`-transitivity
of `MulAction.stabilizer G a` on the complement of `a`.

We define equivariant maps that relate various of these `SubMulAction`s
and permit to manipulate them in a relatively smooth way.

* `SubMulAction.ofStabilizer a` : the action of `stabilizer G a` on `{a}ᶜ`

* `SubMulAction.ENat_card_ofStabilizer_add_one_eq` and `SubMulAction.nat_card_ofStabilizer_eq`
  compute the cardinality of the `carrier` of that action.

Consider `a b : α` and `g : G` such that `hg : g • b = a`.

* `SubMulAction.ofStabilizer.conjMap hg` is the equivariant map
  from `SubMulAction.ofStabilizer G a` to `SubMulAction.ofStabilizer G b`.
* `SubMulAction.ofStabilizer.snoc` : given `x : Fin n ↪ ofStabilizer G a`,
  append `a` to obtain `y : Fin n.succ ↪ α`
-/

@[expose] public section

open scoped Pointwise

open MulAction Function.Embedding

namespace SubMulAction

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]

/-- Action of the stabilizer of a point on the complement. -/
@[to_additive /-- Action of the stabilizer of a point on the complement. -/]
/--
Definition of `ofStabilizer` / `ofStabilizer` 的定义

English:
definition ofStabilizer
  signature: (a : α)
  body: {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not]; rw [smul_eq_iff_eq_inv_smul]
    intro hgx
    apply symm
    rw [hgx]; rw [← smul_eq_iff_eq_inv_smul]
    exact g.prop

@[to_additive]

中文:
定义 ofStabilizer
  签名: (a : α)
  定义体: {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not]; rw [smul_eq_iff_eq_inv_smul]
    intro hgx
    apply symm
    rw [hgx]; rw [← smul_eq_iff_eq_inv_smul]
    exact g.prop

@[to_additive]
-/
def ofStabilizer (a : α) : SubMulAction (stabilizer G a) α where
  carrier := {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not]; rw [smul_eq_iff_eq_inv_smul]
    intro hgx
    apply symm
    rw [hgx]; rw [← smul_eq_iff_eq_inv_smul]
    exact g.prop

@[to_additive]
/--
theorem `ofStabilizer_carrier` / 定理 `ofStabilizer_carrier`

English:
theorem ofStabilizer_carrier
  given: (a : α)
  statement: (ofStabilizer G a).carrier = {a}ᶜ
  proof: rfl

@[to_additive]

中文:
定理 ofStabilizer_carrier
  条件: (a : α)
  结论: (ofStabilizer G a).carrier = {a}ᶜ
  证明: rfl

@[to_additive]
-/
theorem ofStabilizer_carrier (a : α) : (ofStabilizer G a).carrier = {a}ᶜ :=
  rfl

@[to_additive]
/--
theorem `mem_ofStabilizer_iff` / 定理 `mem_ofStabilizer_iff`

English:
theorem mem_ofStabilizer_iff
  given: (a : α) {x : α}
  statement: x in ofStabilizer G a ↔ x != a
  proof: Iff.rfl

@[to_additive]

中文:
定理 mem_ofStabilizer_iff
  条件: (a : α) {x : α}
  结论: x in ofStabilizer G a ↔ x != a
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem mem_ofStabilizer_iff (a : α) {x : α} : x in ofStabilizer G a ↔ x != a :=
  Iff.rfl

@[to_additive]
/--
theorem `notMem_val_image` / 定理 `notMem_val_image`

English:
theorem notMem_val_image
  given: {a : α} (t : Set (ofStabilizer G a))
  proof: by
  rintro ⟨b, hb⟩
  exact b.prop (by simp [hb])

@[to_additive]

中文:
定理 notMem_val_image
  条件: {a : α} (t : Set (ofStabilizer G a))
  证明: by
  rintro ⟨b, hb⟩
  exact b.prop (by simp [hb])

@[to_additive]

Depends on / 依赖: b.prop
-/
theorem notMem_val_image {a : α} (t : Set (ofStabilizer G a)) :
    a ∉ Subtype.val '' t := by
  rintro ⟨b, hb⟩
  exact b.prop (by simp [hb])

@[to_additive]
/--
theorem `neq_of_mem_ofStabilizer` / 定理 `neq_of_mem_ofStabilizer`

English:
theorem neq_of_mem_ofStabilizer
  given: (a : α) {x : ofStabilizer G a}
  statement: ↑x != a
  proof: x.prop

@[to_additive]

中文:
定理 neq_of_mem_ofStabilizer
  条件: (a : α) {x : ofStabilizer G a}
  结论: ↑x != a
  证明: x.prop

@[to_additive]

Depends on / 依赖: x.prop
-/
theorem neq_of_mem_ofStabilizer (a : α) {x : ofStabilizer G a} : ↑x != a :=
  x.prop

@[to_additive]
/--
lemma `ENat_card_ofStabilizer_add_one_eq` / 引理 `ENat_card_ofStabilizer_add_one_eq`

English:
lemma ENat_card_ofStabilizer_add_one_eq
  given: (a : α)
  proof: by
  dsimp only [ENat.card]
  rw [← Cardinal.mk_sum_compl {a}]; rw [map_add]; rw [add_comm]; rw [eq_comm]
  congr
  simp

@[to_additive]

中文:
引理 ENat_card_ofStabilizer_add_one_eq
  条件: (a : α)
  证明: by
  dsimp only [ENat.card]
  rw [← Cardinal.mk_sum_compl {a}]; rw [map_add]; rw [add_comm]; rw [eq_comm]
  congr
  simp

@[to_additive]

Depends on / 依赖: Cardinal, Cardinal.mk_sum_compl, ENat.card, add_comm, eq_comm, map_add, mk_sum_compl
-/
lemma ENat_card_ofStabilizer_add_one_eq (a : α) :
    ENat.card (ofStabilizer G a) + 1 = ENat.card α := by
  dsimp only [ENat.card]
  rw [← Cardinal.mk_sum_compl {a}]; rw [map_add]; rw [add_comm]; rw [eq_comm]
  congr
  simp

@[to_additive]
/--
lemma `nat_card_ofStabilizer_add_one_eq` / 引理 `nat_card_ofStabilizer_add_one_eq`

English:
lemma nat_card_ofStabilizer_add_one_eq
  given: [Finite α] (a : α)
  proof: by
  classical
  let := Fintype.ofFinite α
  rw [Nat.subtype_card {a}ᶜ]; rw [← Finset.card_singleton a]; rw [Finset.card_compl_add_card]; rw [Nat.card_eq_fintype_card]
  simp [mem_ofStabilizer_iff]

@[to_additive]

中文:
引理 nat_card_ofStabilizer_add_one_eq
  条件: [Finite α] (a : α)
  证明: by
  classical
  let := Fintype.ofFinite α
  rw [Nat.subtype_card {a}ᶜ]; rw [← Finset.card_singleton a]; rw [Finset.card_compl_add_card]; rw [Nat.card_eq_fintype_card]
  simp [mem_ofStabilizer_iff]

@[to_additive]

Depends on / 依赖: Finset, Finset.card_compl_add_card, Finset.card_singleton, Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, Nat.subtype_card, card_compl_add_card, card_eq_fintype_card, card_singleton, classical, mem_ofStabilizer_iff, ofFinite, subtype_card
-/
lemma nat_card_ofStabilizer_add_one_eq [Finite α] (a : α) :
    Nat.card (ofStabilizer G a) + 1 = Nat.card α := by
  classical
  let := Fintype.ofFinite α
  rw [Nat.subtype_card {a}ᶜ]; rw [← Finset.card_singleton a]; rw [Finset.card_compl_add_card]; rw [Nat.card_eq_fintype_card]
  simp [mem_ofStabilizer_iff]

@[to_additive]
/--
lemma `nat_card_ofStabilizer_eq` / 引理 `nat_card_ofStabilizer_eq`

English:
lemma nat_card_ofStabilizer_eq
  given: [Finite α] (a : α)
  proof: Nat.eq_sub_of_add_eq (nat_card_ofStabilizer_add_one_eq G a)

中文:
引理 nat_card_ofStabilizer_eq
  条件: [Finite α] (a : α)
  证明: Nat.eq_sub_of_add_eq (nat_card_ofStabilizer_add_one_eq G a)

Depends on / 依赖: Nat.eq_sub_of_add_eq, eq_sub_of_add_eq, nat_card_ofStabilizer_add_one_eq
-/
lemma nat_card_ofStabilizer_eq [Finite α] (a : α) :
    Nat.card (ofStabilizer G a) = Nat.card α - 1 :=
  Nat.eq_sub_of_add_eq (nat_card_ofStabilizer_add_one_eq G a)

variable {G}

/--
Definition of `_root_.SubAddAction.ofStabilizer.conjMap` / `_root_.SubAddAction.ofStabilizer.conjMap` 的定义

English:
definition _root_.SubAddAction.ofStabilizer.conjMap
  signature: {G : Type*} [AddGroup G] {α : Type*} [AddAction G α]
  body: ⟨g +ᵥ x.val, fun hy => x.prop (by simpa [hg] using hy)⟩
  map_vadd' := fun ⟨k, hk⟩ x => by
    simp [← SetLike.coe_eq_coe, AddAction.addSubgroup_vadd_def,
      AddAction.stabilizerEquivStabilizer_apply, ← vadd_assoc]

中文:
定义 _root_.SubAddAction.ofStabilizer.conjMap
  签名: {G : 类型} [AddGroup G] {α : 类型} [AddAction G α]
  定义体: ⟨g +ᵥ x.val, fun hy => x.prop (by simpa [hg] using hy)⟩
  map_vadd' := fun ⟨k, hk⟩ x => by
    simp [← SetLike.coe_eq_coe, AddAction.addSubgroup_vadd_def,
      AddAction.stabilizerEquivStabilizer_apply, ← vadd_assoc]

Depends on / 依赖: x.prop, x.val
-/
def _root_.SubAddAction.ofStabilizer.conjMap {G : Type*} [AddGroup G] {α : Type*} [AddAction G α]
    {g : G} {a b : α} (hg : b = g +ᵥ a) :
    AddActionHom (AddAction.stabilizerEquivStabilizer hg)
      (SubAddAction.ofStabilizer G a) (SubAddAction.ofStabilizer G b) where
  toFun x := ⟨g +ᵥ x.val, fun hy => x.prop (by simpa [hg] using hy)⟩
  map_vadd' := fun ⟨k, hk⟩ x => by
    simp [← SetLike.coe_eq_coe, AddAction.addSubgroup_vadd_def,
      AddAction.stabilizerEquivStabilizer_apply, ← vadd_assoc]

/-- Conjugation induces an equivariant map between the SubMulAction of
the stabilizer of a point and that of its translate. -/
@[to_additive existing SubAddAction.ofStabilizer.conjMap]
/--
Definition of `ofStabilizer.conjMap` / `ofStabilizer.conjMap` 的定义

English:
definition ofStabilizer.conjMap
  signature: {g : G} {a b : α} (hg : b = g • a)
  body: ⟨g • x.val, fun hy => x.prop (by simpa [hg] using hy)⟩
  map_smul' := fun ⟨k, hk⟩ => by
    simp [← SetLike.coe_eq_coe, subgroup_smul_def, stabilizerEquivStabilizer, ← smul_assoc]

中文:
定义 ofStabilizer.conjMap
  签名: {g : G} {a b : α} (hg : b = g • a)
  定义体: ⟨g • x.val, fun hy => x.prop (by simpa [hg] using hy)⟩
  map_smul' := fun ⟨k, hk⟩ => by
    simp [← SetLike.coe_eq_coe, subgroup_smul_def, stabilizerEquivStabilizer, ← smul_assoc]

Depends on / 依赖: x.prop, x.val
-/
def ofStabilizer.conjMap {g : G} {a b : α} (hg : b = g • a) :
    MulActionHom (stabilizerEquivStabilizer hg) (ofStabilizer G a) (ofStabilizer G b) where
  toFun x := ⟨g • x.val, fun hy => x.prop (by simpa [hg] using hy)⟩
  map_smul' := fun ⟨k, hk⟩ => by
    simp [← SetLike.coe_eq_coe, subgroup_smul_def, stabilizerEquivStabilizer, ← smul_assoc]

variable {g h k : G} {a b c : α}
variable (hg : b = g • a) (hh : c = h • b) (hk : c = k • a)

@[to_additive]
/--
theorem `ofStabilizer.conjMap_apply` / 定理 `ofStabilizer.conjMap_apply`

English:
theorem ofStabilizer.conjMap_apply
  given: (x : ofStabilizer G a)
  proof: rfl

中文:
定理 ofStabilizer.conjMap_apply
  条件: (x : ofStabilizer G a)
  证明: rfl
-/
theorem ofStabilizer.conjMap_apply (x : ofStabilizer G a) :
    (conjMap hg x : α) = g • x := rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `_root_.AddAction.stabilizerEquivStabilizer_compTriple` / 定理 `_root_.AddAction.stabilizerEquivStabilizer_compTriple`

English:
theorem _root_.AddAction.stabilizerEquivStabilizer_compTriple
  proof: by
    ext
    simp [AddAction.stabilizerEquivStabilizer, H, AddAut.addConj, ← add_assoc]

中文:
定理 _root_.AddAction.stabilizerEquivStabilizer_compTriple
  证明: by
    ext
    simp [AddAction.stabilizerEquivStabilizer, H, AddAut.addConj, ← add_assoc]

Depends on / 依赖: AddAction, AddAction.stabilizerEquivStabilizer, AddAut, AddAut.addConj, addConj, add_assoc, stabilizerEquivStabilizer
-/
theorem _root_.AddAction.stabilizerEquivStabilizer_compTriple
    {G : Type*} [AddGroup G] {α : Type*} [AddAction G α]
    {g h k : G} {a b c : α} {hg : b = g +ᵥ a} {hh : c = h +ᵥ b} {hk : c = k +ᵥ a} (H : k = h + g) :
    CompTriple (AddAction.stabilizerEquivStabilizer hg)
      (AddAction.stabilizerEquivStabilizer hh) (AddAction.stabilizerEquivStabilizer hk) where
  comp_eq := by
    ext
    simp [AddAction.stabilizerEquivStabilizer, H, AddAut.addConj, ← add_assoc]

set_option backward.isDefEq.respectTransparency false in
variable {hg hh hk} in
@[to_additive existing]
/--
theorem `_root_.MulAction.stabilizerEquivStabilizer_compTriple` / 定理 `_root_.MulAction.stabilizerEquivStabilizer_compTriple`

English:
theorem _root_.MulAction.stabilizerEquivStabilizer_compTriple
  given: (H : k = h * g)
  proof: by
    ext
    simp [stabilizerEquivStabilizer, H, MulAut.conj, ← mul_assoc]

中文:
定理 _root_.MulAction.stabilizerEquivStabilizer_compTriple
  条件: (H : k = h * g)
  证明: by
    ext
    simp [stabilizerEquivStabilizer, H, MulAut.conj, ← mul_assoc]

Depends on / 依赖: MulAut, MulAut.conj, mul_assoc, stabilizerEquivStabilizer
-/
theorem _root_.MulAction.stabilizerEquivStabilizer_compTriple (H : k = h * g) :
    CompTriple (stabilizerEquivStabilizer hg)
      (stabilizerEquivStabilizer hh) (stabilizerEquivStabilizer hk) where
  comp_eq := by
    ext
    simp [stabilizerEquivStabilizer, H, MulAut.conj, ← mul_assoc]

variable {hg hh hk} in
@[to_additive]
/--
theorem `ofStabilizer.conjMap_comp_apply` / 定理 `ofStabilizer.conjMap_comp_apply`

English:
theorem ofStabilizer.conjMap_comp_apply
  given: (H : k = h * g) (x : ofStabilizer G a)
  proof: by
  simp [← Subtype.coe_inj, conjMap_apply, H, mul_smul]

@[to_additive]

中文:
定理 ofStabilizer.conjMap_comp_apply
  条件: (H : k = h * g) (x : ofStabilizer G a)
  证明: by
  simp [← Subtype.coe_inj, conjMap_apply, H, mul_smul]

@[to_additive]

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj, conjMap_apply, mul_smul
-/
theorem ofStabilizer.conjMap_comp_apply (H : k = h * g) (x : ofStabilizer G a) :
    conjMap hh (conjMap hg x) = conjMap hk x := by
  simp [← Subtype.coe_inj, conjMap_apply, H, mul_smul]

@[to_additive]
/--
theorem `ofStabilizer.conjMap_comp_inv_apply` / 定理 `ofStabilizer.conjMap_comp_inv_apply`

English:
theorem ofStabilizer.conjMap_comp_inv_apply
  given: (x : ofStabilizer G a)
  proof: by
  simp [← Subtype.coe_inj, conjMap_apply]

@[to_additive]

中文:
定理 ofStabilizer.conjMap_comp_inv_apply
  条件: (x : ofStabilizer G a)
  证明: by
  simp [← Subtype.coe_inj, conjMap_apply]

@[to_additive]

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj, conjMap_apply
-/
theorem ofStabilizer.conjMap_comp_inv_apply (x : ofStabilizer G a) :
    (conjMap (eq_inv_smul_iff.mpr hg.symm)) (conjMap hg x) = x := by
  simp [← Subtype.coe_inj, conjMap_apply]

@[to_additive]
/--
theorem `ofStabilizer.inv_conjMap_comp_apply` / 定理 `ofStabilizer.inv_conjMap_comp_apply`

English:
theorem ofStabilizer.inv_conjMap_comp_apply
  given: (x : ofStabilizer G b)
  proof: by
  simp [← Subtype.coe_inj, conjMap_apply]

@[to_additive]

中文:
定理 ofStabilizer.inv_conjMap_comp_apply
  条件: (x : ofStabilizer G b)
  证明: by
  simp [← Subtype.coe_inj, conjMap_apply]

@[to_additive]

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj, conjMap_apply
-/
theorem ofStabilizer.inv_conjMap_comp_apply (x : ofStabilizer G b) :
    conjMap hg (conjMap (eq_inv_smul_iff.mpr hg.symm) x) = x := by
  simp [← Subtype.coe_inj, conjMap_apply]

@[to_additive]
/--
theorem `ofStabilizer.conjMap_comp` / 定理 `ofStabilizer.conjMap_comp`

English:
theorem ofStabilizer.conjMap_comp
  given: (H : k = h * g)
  proof: by
  ext x
  simpa using conjMap_comp_apply H x

@[to_additive]

中文:
定理 ofStabilizer.conjMap_comp
  条件: (H : k = h * g)
  证明: by
  ext x
  simpa using conjMap_comp_apply H x

@[to_additive]

Depends on / 依赖: conjMap, conjMap_comp_apply, stabilizerEquivStabilizer_compTriple
-/
theorem ofStabilizer.conjMap_comp (H : k = h * g) :
    (conjMap hh).comp (conjMap hg) (κ := stabilizerEquivStabilizer_compTriple H) = conjMap hk := by
  ext x
  simpa using conjMap_comp_apply H x

@[to_additive]
/--
theorem `ofStabilizer.conjMap_bijective` / 定理 `ofStabilizer.conjMap_bijective`

English:
theorem ofStabilizer.conjMap_bijective
  statement: Function.Bijective (conjMap hg)
  proof: by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    apply (MulAction.injective g)
    rwa [← SetLike.coe_eq_coe, conjMap_apply] at hxy
  · intro x
    exact ⟨conjMap _ x, inv_conjMap_comp_apply _ x⟩

中文:
定理 ofStabilizer.conjMap_bijective
  结论: Function.Bijective (conjMap hg)
  证明: by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    apply (MulAction.injective g)
    rwa [← SetLike.coe_eq_coe, conjMap_apply] at hxy
  · intro x
    exact ⟨conjMap _ x, inv_conjMap_comp_apply _ x⟩

Depends on / 依赖: MulAction, MulAction.injective, SetLike, SetLike.coe_eq_coe, Subtype, Subtype.mk_eq_mk, coe_eq_coe, conjMap, conjMap_apply, injective, inv_conjMap_comp_apply, mk_eq_mk
-/
theorem ofStabilizer.conjMap_bijective : Function.Bijective (conjMap hg) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    apply (MulAction.injective g)
    rwa [← SetLike.coe_eq_coe, conjMap_apply] at hxy
  · intro x
    exact ⟨conjMap _ x, inv_conjMap_comp_apply _ x⟩

/-- Append `a` to `x : Fin n ↪ ofStabilizer G a` to get an element of `Fin n.succ ↪ α`. -/
@[to_additive
  /-- Append `a` to `x : Fin n ↪ ofStabilizer G a` to get an element of `Fin n.succ ↪ α`. -/]
/--
Definition of `ofStabilizer.snoc` / `ofStabilizer.snoc` 的定义

English:
definition ofStabilizer.snoc
  signature: {n : Nat} (x : Fin n ↪ ofStabilizer G a)
  body: Fin.Embedding.snoc (x.trans (subtype _)) (a := a) (by
    simp only [Set.mem_range, trans_apply, Function.Embedding.subtype_apply, not_exists]
    exact fun i => (x i).prop)

@[to_additive]

中文:
定义 ofStabilizer.snoc
  签名: {n : 自然数} (x : Fin n ↪ ofStabilizer G a)
  定义体: Fin.Embedding.snoc (x.trans (subtype _)) (a := a) (by
    simp only [Set.mem_range, trans_apply, Function.Embedding.subtype_apply, not_exists]
    exact fun i => (x i).prop)

@[to_additive]

Depends on / 依赖: Embedding, Fin.Embedding.snoc, Function, Function.Embedding.subtype_apply, Set.mem_range, mem_range, not_exists, subtype, subtype_apply, trans_apply, x.trans
-/
def ofStabilizer.snoc {n : Nat} (x : Fin n ↪ ofStabilizer G a) :
    Fin n.succ ↪ α :=
  Fin.Embedding.snoc (x.trans (subtype _)) (a := a) (by
    simp only [Set.mem_range, trans_apply, Function.Embedding.subtype_apply, not_exists]
    exact fun i => (x i).prop)

@[to_additive]
/--
theorem `ofStabilizer.snoc_castSucc` / 定理 `ofStabilizer.snoc_castSucc`

English:
theorem ofStabilizer.snoc_castSucc
  given: {n : Nat} (x : Fin n ↪ ofStabilizer G a) (i : Fin n)
  proof: by
  simp [snoc]

@[to_additive]

中文:
定理 ofStabilizer.snoc_castSucc
  条件: {n : 自然数} (x : Fin n ↪ ofStabilizer G a) (i : Fin n)
  证明: by
  simp [snoc]

@[to_additive]
-/
theorem ofStabilizer.snoc_castSucc {n : Nat} (x : Fin n ↪ ofStabilizer G a) (i : Fin n) :
    snoc x i.castSucc = x i := by
  simp [snoc]

@[to_additive]
/--
theorem `ofStabilizer.snoc_last` / 定理 `ofStabilizer.snoc_last`

English:
theorem ofStabilizer.snoc_last
  given: {n : Nat} (x : Fin n ↪ ofStabilizer G a)
  proof: by
  simp [snoc]

中文:
定理 ofStabilizer.snoc_last
  条件: {n : 自然数} (x : Fin n ↪ ofStabilizer G a)
  证明: by
  simp [snoc]
-/
theorem ofStabilizer.snoc_last {n : Nat} (x : Fin n ↪ ofStabilizer G a) :
    snoc x (Fin.last n) = a := by
  simp [snoc]

variable (G) in
@[to_additive]
/--
lemma `exists_smul_of_last_eq` / 引理 `exists_smul_of_last_eq`

English:
lemma exists_smul_of_last_eq
  given: [IsPretransitive G α] {n : Nat} (a : α) (x : Fin n.succ ↪ α)
  proof: by
  obtain ⟨g, hgx⟩ := exists_smul_eq G (x (Fin.last n)) a
  have H : forall i, Fin.Embedding.init (g • x) i in ofStabilizer G a := fun i => by
    simp only [mem_ofStabilizer_iff,
      Nat.succ_eq_add_one, ← hgx, ← smul_apply, ne_eq]
    suffices Fin.Embedding.init (g • x) i = (g • x) i.castSucc 

中文:
引理 exists_smul_of_last_eq
  条件: [IsPretransitive G α] {n : 自然数} (a : α) (x : Fin n.succ ↪ α)
  证明: by
  obtain ⟨g, hgx⟩ := exists_smul_eq G (x (Fin.last n)) a
  have H : forall i, Fin.Embedding.init (g • x) i in ofStabilizer G a := fun i => by
    simp only [mem_ofStabilizer_iff,
      Nat.succ_eq_add_one, ← hgx, ← smul_apply, ne_eq]
    suffices Fin.Embedding.init (g • x) i = (g • x) i.castSucc 

Depends on / 依赖: Embedding, Fin.Embedding.init, Fin.eq_castSucc_or_eq_last, Fin.init_def, Fin.last, Nat.succ_eq_add_one, castSucc, codRestrict, eq_castSucc_or_eq_last, exists_smul_eq, i.castSucc, init_def, mem_ofStabilizer_iff, ne_eq, ofStabilizer, ofStabilizer.snoc, smul_apply, succ_eq_add_one
-/
lemma exists_smul_of_last_eq [IsPretransitive G α] {n : Nat} (a : α) (x : Fin n.succ ↪ α) :
    exists (g : G) (y : Fin n ↪ ofStabilizer G a), g • x = ofStabilizer.snoc y := by
  obtain ⟨g, hgx⟩ := exists_smul_eq G (x (Fin.last n)) a
  have H : forall i, Fin.Embedding.init (g • x) i in ofStabilizer G a := fun i => by
    simp only [mem_ofStabilizer_iff,
      Nat.succ_eq_add_one, ← hgx, ← smul_apply, ne_eq]
    suffices Fin.Embedding.init (g • x) i = (g • x) i.castSucc by
      simp [this]
    simp [Fin.Embedding.init, Fin.init_def]
  use g, (Fin.Embedding.init (g • x)).codRestrict (ofStabilizer G a) H
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
  · simpa [ofStabilizer.snoc] using!
Subtype.ext_iff.mp Function.Embedding.codRestrict_apply _ _ H i
  · simpa only [smul_apply, ofStabilizer.snoc, Fin.Embedding.snoc_last]

end SubMulAction

section Pointwise

open MulAction Set

variable (G : Type*) [Group G] (α : Type*) [MulAction G α]

/-- The stabilizer of a set acts on that set. -/
@[to_additive /-- The stabilizer of a set acts on that set. -/]
/--
Instance `_root_.SMul.ofStabilizer` / 实例 `_root_.SMul.ofStabilizer`

English:
instance _root_.SMul.ofStabilizer
  signature: (s : Set α)
  body: ⟨g • ↑x, by
    convert! Set.smul_mem_smul_set x.prop
    exact (mem_stabilizer_iff.mp g.prop).symm⟩

@[simp]

中文:
实例 _root_.SMul.ofStabilizer
  签名: (s : Set α)
  定义体: ⟨g • ↑x, by
    convert! Set.smul_mem_smul_set x.prop
    exact (mem_stabilizer_iff.mp g.prop).symm⟩

@[simp]

Depends on / 依赖: Set.smul_mem_smul_set, convert, g.prop, mem_stabilizer_iff, mem_stabilizer_iff.mp, smul_mem_smul_set, x.prop
-/
instance _root_.SMul.ofStabilizer (s : Set α) :
    SMul (stabilizer G s) s where
  smul g x := ⟨g • ↑x, by
    convert! Set.smul_mem_smul_set x.prop
    exact (mem_stabilizer_iff.mp g.prop).symm⟩

@[simp]
/--
theorem `_root_.SMul.smul_stabilizer_def` / 定理 `_root_.SMul.smul_stabilizer_def`

English:
theorem _root_.SMul.smul_stabilizer_def
  given: (s : Set α) (g : stabilizer G s) (x : s)
  proof: rfl

中文:
定理 _root_.SMul.smul_stabilizer_def
  条件: (s : Set α) (g : stabilizer G s) (x : s)
  证明: rfl
-/
theorem _root_.SMul.smul_stabilizer_def (s : Set α) (g : stabilizer G s) (x : s) :
    ((g • x : ↥s) : α) = (g : G) • (x : α) :=
  rfl

/-- The stabilizer of a set acts on that set -/
@[to_additive /-- The stabilizer of a set acts on that set. -/]
instance (s : Set α) : MulAction (stabilizer G s) s where
  one_smul x := by
    simp only [← Subtype.coe_inj, SMul.smul_stabilizer_def, OneMemClass.coe_one, one_smul]
  mul_smul g k x := by
    simp only [← Subtype.coe_inj, SMul.smul_stabilizer_def, Subgroup.coe_mul, mul_smul]

/--
theorem `stabilizer_empty_eq_top` / 定理 `stabilizer_empty_eq_top`

English:
theorem stabilizer_empty_eq_top
  proof: by
  aesop

中文:
定理 stabilizer_empty_eq_top
  证明: by
  aesop
-/
theorem stabilizer_empty_eq_top :
    stabilizer G (∅ : Set α) = ⊤ := by
  aesop

/--
theorem `stabilizer_univ_eq_top` / 定理 `stabilizer_univ_eq_top`

English:
theorem stabilizer_univ_eq_top
  proof: by
  aesop

中文:
定理 stabilizer_univ_eq_top
  证明: by
  aesop
-/
theorem stabilizer_univ_eq_top :
    stabilizer G (Set.univ : Set α) = ⊤ := by
  aesop

/-- The stabilizer of the complement is the stabilizer of the set. -/
@[simp]
/--
theorem `stabilizer_compl` / 定理 `stabilizer_compl`

English:
theorem stabilizer_compl
  given: {s : Set α}
  proof: by
  have (s : Set α) : stabilizer G s <= stabilizer G (sᶜ) := by
    intro g h
    simp [Set.smul_set_compl, mem_stabilizer_iff.1 h]
  refine le_antisymm (le_of_le_of_eq (this _) ?_) (this _)
  rw [compl_compl]

中文:
定理 stabilizer_compl
  条件: {s : Set α}
  证明: by
  have (s : Set α) : stabilizer G s <= stabilizer G (sᶜ) := by
    intro g h
    simp [Set.smul_set_compl, mem_stabilizer_iff.1 h]
  refine le_antisymm (le_of_le_of_eq (this _) ?_) (this _)
  rw [compl_compl]

Depends on / 依赖: Set.smul_set_compl, compl_compl, le_antisymm, le_of_le_of_eq, mem_stabilizer_iff, smul_set_compl, stabilizer
-/
theorem stabilizer_compl {s : Set α} :
    stabilizer G sᶜ = stabilizer G s := by
  have (s : Set α) : stabilizer G s <= stabilizer G (sᶜ) := by
    intro g h
    simp [Set.smul_set_compl, mem_stabilizer_iff.1 h]
  refine le_antisymm (le_of_le_of_eq (this _) ?_) (this _)
  rw [compl_compl]

end Pointwise
