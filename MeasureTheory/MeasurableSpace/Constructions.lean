/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Update
public import Mathlib.Data.Prod.TProd
public import Mathlib.Data.Set.UnionLift
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Mathlib.Order.Disjointed

/-!
# Constructions for measurable spaces and functions

This file provides several ways to construct new measurable spaces and functions from old ones:
`Quotient`, `Subtype`, `Prod`, `Pi`, etc.
-/

@[expose] public section

assert_not_exists Filter

open Set Function

universe uι

variable {α β γ δ δ' : Type*} {ι : Sort uι} {s : Set α}

/--
theorem `measurable_to_countable` / 定理 `measurable_to_countable`

English:
theorem measurable_to_countable
  statement: [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β -> α}
  proof: fun s _ => by
  rw [← biUnion_preimage_singleton]
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy => ?_
  by_cases hyf : y in range f
  · rcases hyf with ⟨y, rfl⟩
    apply h
  · simp only [preimage_singleton_eq_empty.2 hyf, MeasurableSet.empty]

中文:
定理 measurable_to_countable
  结论: [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β -> α}
  证明: fun s _ => by
  rw [← biUnion_preimage_singleton]
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy => ?_
  by_cases hyf : y in range f
  · rcases hyf with ⟨y, rfl⟩
    apply h
  · simp only [preimage_singleton_eq_empty.2 hyf, MeasurableSet.empty]

Depends on / 依赖: MeasurableSet, MeasurableSet.empty, MeasurableSet.iUnion, biUnion_preimage_singleton, iUnion, preimage_singleton_eq_empty
-/
theorem measurable_to_countable [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β -> α}
    (h : forall y, MeasurableSet (f ⁻¹' {f y})) : Measurable f := fun s _ => by
  rw [← biUnion_preimage_singleton]
  refine MeasurableSet.iUnion fun y => MeasurableSet.iUnion fun hy => ?_
  by_cases hyf : y in range f
  · rcases hyf with ⟨y, rfl⟩
    apply h
  · simp only [preimage_singleton_eq_empty.2 hyf, MeasurableSet.empty]

/--
theorem `measurable_to_countable'` / 定理 `measurable_to_countable'`

English:
theorem measurable_to_countable'
  statement: [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β -> α}
  proof: measurable_to_countable fun y => h (f y)

中文:
定理 measurable_to_countable'
  结论: [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β -> α}
  证明: measurable_to_countable fun y => h (f y)

Depends on / 依赖: measurable_to_countable
-/
theorem measurable_to_countable' [MeasurableSpace α] [Countable α] [MeasurableSpace β] {f : β -> α}
    (h : forall x, MeasurableSet (f ⁻¹' {x})) : Measurable f :=
  measurable_to_countable fun y => h (f y)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ENat.measurable_iff` / 定理 `ENat.measurable_iff`

English:
theorem ENat.measurable_iff
  given: {α : Type*} [MeasurableSpace α] {f : α -> Nat∞}
  proof: by
refine ⟨fun hf n => hf measurableSet_singleton _, fun h => measurable_to_countable' fun n => ?_⟩
  cases n with
  | top =>
    rw [← WithTop.none_eq_top]; rw [← compl_range_some]; rw [preimage_compl]; rw [← iUnion_singleton_eq_range]; rw [preimage_iUnion]
exact .compl .iUnion h
  | coe n => exact

中文:
定理 ENat.measurable_iff
  条件: {α : 类型} [MeasurableSpace α] {f : α -> 自然数∞}
  证明: by
refine ⟨fun hf n => hf measurableSet_singleton _, fun h => measurable_to_countable' fun n => ?_⟩
  cases n with
  | top =>
    rw [← WithTop.none_eq_top]; rw [← compl_range_some]; rw [preimage_compl]; rw [← iUnion_singleton_eq_range]; rw [preimage_iUnion]
exact .compl .iUnion h
  | coe n => exact

Depends on / 依赖: WithTop, WithTop.none_eq_top, compl_range_some, iUnion, iUnion_singleton_eq_range, measurableSet_singleton, measurable_to_countable, none_eq_top, preimage_compl, preimage_iUnion
-/
theorem ENat.measurable_iff {α : Type*} [MeasurableSpace α] {f : α -> Nat∞} :
    Measurable f ↔ forall n : Nat, MeasurableSet (f ⁻¹' {↑n}) := by
refine ⟨fun hf n => hf measurableSet_singleton _, fun h => measurable_to_countable' fun n => ?_⟩
  cases n with
  | top =>
    rw [← WithTop.none_eq_top]; rw [← compl_range_some]; rw [preimage_compl]; rw [← iUnion_singleton_eq_range]; rw [preimage_iUnion]
exact .compl .iUnion h
  | coe n => exact h n

/--
theorem `measurable_unit` / 定理 `measurable_unit`

English:
theorem measurable_unit
  given: [MeasurableSpace α] (f : Unit -> α)
  statement: Measurable f
  proof: measurable_from_top

中文:
定理 measurable_unit
  条件: [MeasurableSpace α] (f : Unit -> α)
  结论: Measurable f
  证明: measurable_from_top

Depends on / 依赖: measurable_from_top
-/
theorem measurable_unit [MeasurableSpace α] (f : Unit -> α) : Measurable f :=
  measurable_from_top

section ULift
variable [MeasurableSpace α]

/--
Instance `_root_.ULift.instMeasurableSpace` / 实例 `_root_.ULift.instMeasurableSpace`

English:
instance _root_.ULift.instMeasurableSpace
  signature: : MeasurableSpace (ULift α)
  body: ‹MeasurableSpace α›.map ULift.up

中文:
实例 _root_.ULift.instMeasurableSpace
  签名: : MeasurableSpace (ULift α)
  定义体: ‹MeasurableSpace α›.map ULift.up

Depends on / 依赖: MeasurableSpace, ULift.up
-/
instance _root_.ULift.instMeasurableSpace : MeasurableSpace (ULift α) :=
  ‹MeasurableSpace α›.map ULift.up

/--
lemma `measurable_down` / 引理 `measurable_down`

English:
lemma measurable_down
  statement: Measurable (ULift.down : ULift α -> α)
  proof: fun _ => id

中文:
引理 measurable_down
  结论: Measurable (ULift.down : ULift α -> α)
  证明: fun _ => id
-/
lemma measurable_down : Measurable (ULift.down : ULift α -> α) := fun _ => id
/--
lemma `measurable_up` / 引理 `measurable_up`

English:
lemma measurable_up
  statement: Measurable (ULift.up : α -> ULift α)
  proof: fun _ => id

中文:
引理 measurable_up
  结论: Measurable (ULift.up : α -> ULift α)
  证明: fun _ => id
-/
lemma measurable_up : Measurable (ULift.up : α -> ULift α) := fun _ => id

/--
lemma `measurableSet_preimage_down` / 引理 `measurableSet_preimage_down`

English:
lemma measurableSet_preimage_down
  given: {s : Set α}
  proof: Iff.rfl

中文:
引理 measurableSet_preimage_down
  条件: {s : Set α}
  证明: Iff.rfl
-/
@[simp] lemma measurableSet_preimage_down {s : Set α} :
    MeasurableSet (ULift.down ⁻¹' s) ↔ MeasurableSet s := Iff.rfl
/--
lemma `measurableSet_preimage_up` / 引理 `measurableSet_preimage_up`

English:
lemma measurableSet_preimage_up
  given: {s : Set (ULift α)}
  proof: Iff.rfl

中文:
引理 measurableSet_preimage_up
  条件: {s : Set (ULift α)}
  证明: Iff.rfl
-/
@[simp] lemma measurableSet_preimage_up {s : Set (ULift α)} :
    MeasurableSet (ULift.up ⁻¹' s) ↔ MeasurableSet s := Iff.rfl

end ULift

section Nat

variable {mα : MeasurableSpace α}

/--
theorem `measurable_from_nat` / 定理 `measurable_from_nat`

English:
theorem measurable_from_nat
  given: {f : Nat -> α}
  statement: Measurable f
  proof: measurable_from_top

中文:
定理 measurable_from_nat
  条件: {f : 自然数 -> α}
  结论: Measurable f
  证明: measurable_from_top

Depends on / 依赖: measurable_from_top
-/
theorem measurable_from_nat {f : Nat -> α} : Measurable f :=
  measurable_from_top

/--
theorem `measurable_to_nat` / 定理 `measurable_to_nat`

English:
theorem measurable_to_nat
  given: {f : α -> Nat}
  statement: (forall y, MeasurableSet (f ⁻¹' {f y})) -> Measurable f
  proof: measurable_to_countable

中文:
定理 measurable_to_nat
  条件: {f : α -> 自然数}
  结论: (对任意 y, MeasurableSet (f ⁻¹' {f y})) -> Measurable f
  证明: measurable_to_countable

Depends on / 依赖: measurable_to_countable
-/
theorem measurable_to_nat {f : α -> Nat} : (forall y, MeasurableSet (f ⁻¹' {f y})) -> Measurable f :=
  measurable_to_countable

/--
theorem `measurable_to_bool` / 定理 `measurable_to_bool`

English:
theorem measurable_to_bool
  given: {f : α -> Bool} (h : MeasurableSet (f ⁻¹' {true}))
  statement: Measurable f
  proof: by
  apply measurable_to_countable'
  rintro (- | -)
  · convert! h.compl
    rw [← preimage_compl]; rw [Bool.compl_singleton]; rw [Bool.not_true]
  exact h

中文:
定理 measurable_to_bool
  条件: {f : α -> 布尔} (h : MeasurableSet (f ⁻¹' {true}))
  结论: Measurable f
  证明: by
  apply measurable_to_countable'
  rintro (- | -)
  · convert! h.compl
    rw [← preimage_compl]; rw [Bool.compl_singleton]; rw [Bool.not_true]
  exact h

Depends on / 依赖: Bool.compl_singleton, Bool.not_true, compl_singleton, convert, h.compl, measurable_to_countable, not_true, preimage_compl
-/
theorem measurable_to_bool {f : α -> Bool} (h : MeasurableSet (f ⁻¹' {true})) : Measurable f := by
  apply measurable_to_countable'
  rintro (- | -)
  · convert! h.compl
    rw [← preimage_compl]; rw [Bool.compl_singleton]; rw [Bool.not_true]
  exact h

/--
theorem `measurable_to_prop` / 定理 `measurable_to_prop`

English:
theorem measurable_to_prop
  given: {f : α -> Prop} (h : MeasurableSet (f ⁻¹' {True}))
  statement: Measurable f
  proof: by
  refine measurable_to_countable' fun x => ?_
  by_cases hx : x
  · simpa [hx] using h
  · simpa only [hx, ← preimage_compl, Prop.compl_singleton, not_true, preimage_singleton_false]
      using h.compl

中文:
定理 measurable_to_prop
  条件: {f : α -> 命题} (h : MeasurableSet (f ⁻¹' {True}))
  结论: Measurable f
  证明: by
  refine measurable_to_countable' fun x => ?_
  by_cases hx : x
  · simpa [hx] using h
  · simpa only [hx, ← preimage_compl, Prop.compl_singleton, not_true, preimage_singleton_false]
      using h.compl

Depends on / 依赖: Prop.compl_singleton, compl_singleton, h.compl, measurable_to_countable, not_true, preimage_compl, preimage_singleton_false
-/
theorem measurable_to_prop {f : α -> Prop} (h : MeasurableSet (f ⁻¹' {True})) : Measurable f := by
  refine measurable_to_countable' fun x => ?_
  by_cases hx : x
  · simpa [hx] using h
  · simpa only [hx, ← preimage_compl, Prop.compl_singleton, not_true, preimage_singleton_false]
      using h.compl

/--
theorem `measurable_findGreatest'` / 定理 `measurable_findGreatest'`

English:
theorem measurable_findGreatest'
  statement: {p : α -> Nat -> Prop} [forall x, DecidablePred (p x)] {N : Nat}
  proof: measurable_to_nat fun _ => hN _ N.findGreatest_le

中文:
定理 measurable_findGreatest'
  结论: {p : α -> 自然数 -> 命题} [对任意 x, DecidablePred (p x)] {N : 自然数}
  证明: measurable_to_nat fun _ => hN _ N.findGreatest_le

Depends on / 依赖: N.findGreatest_le, findGreatest_le, measurable_to_nat
-/
theorem measurable_findGreatest' {p : α -> Nat -> Prop} [forall x, DecidablePred (p x)] {N : Nat}
    (hN : forall k <= N, MeasurableSet { x | Nat.findGreatest (p x) N = k }) :
    Measurable fun x => Nat.findGreatest (p x) N :=
  measurable_to_nat fun _ => hN _ N.findGreatest_le

/--
theorem `measurable_findGreatest` / 定理 `measurable_findGreatest`

English:
theorem measurable_findGreatest
  statement: {p : α -> Nat -> Prop} [forall x, DecidablePred (p x)] {N}
  proof: by
  refine measurable_findGreatest' fun k hk => ?_
  simp only [Nat.findGreatest_eq_iff, ofPred_and, ofPred_forall, ← compl_ofPred]
  repeat' apply_rules [MeasurableSet.inter, MeasurableSet.const, MeasurableSet.iInter,
    MeasurableSet.compl, hN] <;> try intros

@[simp, measurability]

中文:
定理 measurable_findGreatest
  结论: {p : α -> 自然数 -> 命题} [对任意 x, DecidablePred (p x)] {N}
  证明: by
  refine measurable_findGreatest' fun k hk => ?_
  simp only [Nat.findGreatest_eq_iff, ofPred_and, ofPred_forall, ← compl_ofPred]
  repeat' apply_rules [MeasurableSet.inter, MeasurableSet.const, MeasurableSet.iInter,
    MeasurableSet.compl, hN] <;> try intros

@[simp, measurability]

Depends on / 依赖: MeasurableSet, MeasurableSet.compl, MeasurableSet.const, MeasurableSet.iInter, MeasurableSet.inter, Nat.findGreatest_eq_iff, apply_rules, compl_ofPred, findGreatest_eq_iff, iInter, intros, measurable_findGreatest, ofPred_and, ofPred_forall, repeat
-/
theorem measurable_findGreatest {p : α -> Nat -> Prop} [forall x, DecidablePred (p x)] {N}
    (hN : forall k <= N, MeasurableSet { x | p x k }) : Measurable fun x => Nat.findGreatest (p x) N := by
  refine measurable_findGreatest' fun k hk => ?_
  simp only [Nat.findGreatest_eq_iff, ofPred_and, ofPred_forall, ← compl_ofPred]
  repeat' apply_rules [MeasurableSet.inter, MeasurableSet.const, MeasurableSet.iInter,
    MeasurableSet.compl, hN] <;> try intros

@[simp, measurability]
/--
theorem `MeasurableSet.disjointed` / 定理 `MeasurableSet.disjointed`

English:
theorem MeasurableSet.disjointed
  given: {f : Nat -> Set α} (h : forall i, MeasurableSet (f i)) (n)
  proof: disjointedRec (fun _ _ ht => MeasurableSet.diff ht <| h _) (h n)

中文:
定理 MeasurableSet.disjointed
  条件: {f : 自然数 -> Set α} (h : 对任意 i, MeasurableSet (f i)) (n)
  证明: disjointedRec (fun _ _ ht => MeasurableSet.diff ht <| h _) (h n)
-/
protected theorem MeasurableSet.disjointed {f : Nat -> Set α} (h : forall i, MeasurableSet (f i)) (n) :
    MeasurableSet (disjointed f n) :=
  disjointedRec (fun _ _ ht => MeasurableSet.diff ht <| h _) (h n)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `measurable_find` / 定理 `measurable_find`

English:
theorem measurable_find
  statement: {p : α -> Nat -> Prop} [forall x, DecidablePred (p x)] (hp : forall x, exists N, p x N)
  proof: by
  refine measurable_to_nat fun x => ?_
  rw [preimage_find_eq_disjointed (fun k => {x | p x k})]
  exact MeasurableSet.disjointed hm _

中文:
定理 measurable_find
  结论: {p : α -> 自然数 -> 命题} [对任意 x, DecidablePred (p x)] (hp : 对任意 x, 存在 N, p x N)
  证明: by
  refine measurable_to_nat fun x => ?_
  rw [preimage_find_eq_disjointed (fun k => {x | p x k})]
  exact MeasurableSet.disjointed hm _

Depends on / 依赖: MeasurableSet, MeasurableSet.disjointed, disjointed, measurable_to_nat, preimage_find_eq_disjointed
-/
theorem measurable_find {p : α -> Nat -> Prop} [forall x, DecidablePred (p x)] (hp : forall x, exists N, p x N)
    (hm : forall k, MeasurableSet { x | p x k }) : Measurable fun x => Nat.find (hp x) := by
  refine measurable_to_nat fun x => ?_
  rw [preimage_find_eq_disjointed (fun k => {x | p x k})]
  exact MeasurableSet.disjointed hm _

end Nat

section Quotient

variable [MeasurableSpace α] [MeasurableSpace β]

/--
Instance `Quot.instMeasurableSpace` / 实例 `Quot.instMeasurableSpace`

English:
instance Quot.instMeasurableSpace
  signature: {α} {r : α -> α -> Prop} [m : MeasurableSpace α]
  body: m.map (Quot.mk r)

中文:
实例 Quot.instMeasurableSpace
  签名: {α} {r : α -> α -> 命题} [m : MeasurableSpace α]
  定义体: m.map (Quot.mk r)

Depends on / 依赖: Quot.mk, m.map
-/
instance Quot.instMeasurableSpace {α} {r : α -> α -> Prop} [m : MeasurableSpace α] :
    MeasurableSpace (Quot r) :=
  m.map (Quot.mk r)

/--
Instance `Quotient.instMeasurableSpace` / 实例 `Quotient.instMeasurableSpace`

English:
instance Quotient.instMeasurableSpace
  signature: {α} {s : Setoid α} [m : MeasurableSpace α]
  body: m.map Quotient.mk''

@[to_additive]

中文:
实例 Quotient.instMeasurableSpace
  签名: {α} {s : Setoid α} [m : MeasurableSpace α]
  定义体: m.map Quotient.mk''

@[to_additive]

Depends on / 依赖: Quotient, Quotient.mk, m.map
-/
instance Quotient.instMeasurableSpace {α} {s : Setoid α} [m : MeasurableSpace α] :
    MeasurableSpace (Quotient s) :=
  m.map Quotient.mk''

@[to_additive]
/--
Instance `QuotientGroup.measurableSpace` / 实例 `QuotientGroup.measurableSpace`

English:
instance QuotientGroup.measurableSpace
  signature: {G} [Group G] [MeasurableSpace G] (S : Subgroup G)
  body: Quotient.instMeasurableSpace

中文:
实例 QuotientGroup.measurableSpace
  签名: {G} [Group G] [MeasurableSpace G] (S : Subgroup G)
  定义体: Quotient.instMeasurableSpace

Depends on / 依赖: Quotient, Quotient.instMeasurableSpace, instMeasurableSpace
-/
instance QuotientGroup.measurableSpace {G} [Group G] [MeasurableSpace G] (S : Subgroup G) :
    MeasurableSpace (G ⧸ S) :=
  Quotient.instMeasurableSpace

/--
theorem `measurableSet_quotient` / 定理 `measurableSet_quotient`

English:
theorem measurableSet_quotient
  given: {s : Setoid α} {t : Set (Quotient s)}
  proof: Iff.rfl

中文:
定理 measurableSet_quotient
  条件: {s : Setoid α} {t : Set (Quotient s)}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem measurableSet_quotient {s : Setoid α} {t : Set (Quotient s)} :
    MeasurableSet t ↔ MeasurableSet (Quotient.mk'' ⁻¹' t) :=
  Iff.rfl

/--
theorem `measurable_from_quotient` / 定理 `measurable_from_quotient`

English:
theorem measurable_from_quotient
  given: {s : Setoid α} {f : Quotient s -> β}
  proof: Iff.rfl

@[fun_prop]

中文:
定理 measurable_from_quotient
  条件: {s : Setoid α} {f : Quotient s -> β}
  证明: Iff.rfl

@[fun_prop]

Depends on / 依赖: Iff.rfl
-/
theorem measurable_from_quotient {s : Setoid α} {f : Quotient s -> β} :
    Measurable f ↔ Measurable (f ∘ Quotient.mk'') :=
  Iff.rfl

@[fun_prop]
/--
theorem `measurable_quotient_mk'` / 定理 `measurable_quotient_mk'`

English:
theorem measurable_quotient_mk'
  given: [s : Setoid α]
  statement: Measurable (Quotient.mk' : α -> Quotient s)
  proof: fun _ => id

@[fun_prop]

中文:
定理 measurable_quotient_mk'
  条件: [s : Setoid α]
  结论: Measurable (Quotient.mk' : α -> Quotient s)
  证明: fun _ => id

@[fun_prop]
-/
theorem measurable_quotient_mk' [s : Setoid α] : Measurable (Quotient.mk' : α -> Quotient s) :=
  fun _ => id

@[fun_prop]
/--
theorem `measurable_quotient_mk''` / 定理 `measurable_quotient_mk''`

English:
theorem measurable_quotient_mk''
  given: {s : Setoid α}
  statement: Measurable (Quotient.mk'' : α -> Quotient s)
  proof: fun _ => id

@[fun_prop]

中文:
定理 measurable_quotient_mk''
  条件: {s : Setoid α}
  结论: Measurable (Quotient.mk'' : α -> Quotient s)
  证明: fun _ => id

@[fun_prop]
-/
theorem measurable_quotient_mk'' {s : Setoid α} : Measurable (Quotient.mk'' : α -> Quotient s) :=
  fun _ => id

@[fun_prop]
/--
theorem `measurable_quot_mk` / 定理 `measurable_quot_mk`

English:
theorem measurable_quot_mk
  given: {r : α -> α -> Prop}
  statement: Measurable (Quot.mk r)
  proof: fun _ => id

@[to_additive (attr := fun_prop)]

中文:
定理 measurable_quot_mk
  条件: {r : α -> α -> 命题}
  结论: Measurable (Quot.mk r)
  证明: fun _ => id

@[to_additive (attr := fun_prop)]
-/
theorem measurable_quot_mk {r : α -> α -> Prop} : Measurable (Quot.mk r) := fun _ => id

@[to_additive (attr := fun_prop)]
/--
theorem `QuotientGroup.measurable_coe` / 定理 `QuotientGroup.measurable_coe`

English:
theorem QuotientGroup.measurable_coe
  given: {G} [Group G] [MeasurableSpace G] {S : Subgroup G}
  proof: measurable_quotient_mk''

@[to_additive]
nonrec theorem QuotientGroup.measurable_from_quotient {G} [Group G] [MeasurableSpace G]
    {S : Subgroup G} {f : G ⧸ S -> α} : Measurable f ↔ Measurable (f ∘ ((↑) : G -> G ⧸ S)) :=
  measurable_from_quotient

中文:
定理 QuotientGroup.measurable_coe
  条件: {G} [Group G] [MeasurableSpace G] {S : Subgroup G}
  证明: measurable_quotient_mk''

@[to_additive]
nonrec theorem QuotientGroup.measurable_from_quotient {G} [Group G] [MeasurableSpace G]
    {S : Subgroup G} {f : G ⧸ S -> α} : Measurable f ↔ Measurable (f ∘ ((↑) : G -> G ⧸ S)) :=
  measurable_from_quotient

Depends on / 依赖: measurable_quotient_mk
-/
theorem QuotientGroup.measurable_coe {G} [Group G] [MeasurableSpace G] {S : Subgroup G} :
    Measurable ((↑) : G -> G ⧸ S) :=
  measurable_quotient_mk''

@[to_additive]
nonrec theorem QuotientGroup.measurable_from_quotient {G} [Group G] [MeasurableSpace G]
    {S : Subgroup G} {f : G ⧸ S -> α} : Measurable f ↔ Measurable (f ∘ ((↑) : G -> G ⧸ S)) :=
  measurable_from_quotient

/--
Instance `Quotient.instDiscreteMeasurableSpace` / 实例 `Quotient.instDiscreteMeasurableSpace`

English:
instance Quotient.instDiscreteMeasurableSpace
  signature: {α} {s : Setoid α} [MeasurableSpace α]
  body: measurableSet_quotient.2 .of_discrete

@[to_additive]

中文:
实例 Quotient.instDiscreteMeasurableSpace
  签名: {α} {s : Setoid α} [MeasurableSpace α]
  定义体: measurableSet_quotient.2 .of_discrete

@[to_additive]

Depends on / 依赖: measurableSet_quotient, of_discrete
-/
instance Quotient.instDiscreteMeasurableSpace {α} {s : Setoid α} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] : DiscreteMeasurableSpace (Quotient s) where
  forall_measurableSet _ := measurableSet_quotient.2 .of_discrete

@[to_additive]
/--
Instance `QuotientGroup.instDiscreteMeasurableSpace` / 实例 `QuotientGroup.instDiscreteMeasurableSpace`

English:
instance QuotientGroup.instDiscreteMeasurableSpace
  signature: {G} [Group G] [MeasurableSpace G]
  body: Quotient.instDiscreteMeasurableSpace

中文:
实例 QuotientGroup.instDiscreteMeasurableSpace
  签名: {G} [Group G] [MeasurableSpace G]
  定义体: Quotient.instDiscreteMeasurableSpace

Depends on / 依赖: Quotient, Quotient.instDiscreteMeasurableSpace, instDiscreteMeasurableSpace
-/
instance QuotientGroup.instDiscreteMeasurableSpace {G} [Group G] [MeasurableSpace G]
    [DiscreteMeasurableSpace G] (S : Subgroup G) : DiscreteMeasurableSpace (G ⧸ S) :=
  Quotient.instDiscreteMeasurableSpace

end Quotient

section Subtype

/--
Instance `Subtype.instMeasurableSpace` / 实例 `Subtype.instMeasurableSpace`

English:
instance Subtype.instMeasurableSpace
  signature: {α} {p : α -> Prop} [m : MeasurableSpace α]
  body: m.comap ((↑) : _ -> α)

中文:
实例 Subtype.instMeasurableSpace
  签名: {α} {p : α -> 命题} [m : MeasurableSpace α]
  定义体: m.comap ((↑) : _ -> α)

Depends on / 依赖: m.comap
-/
instance Subtype.instMeasurableSpace {α} {p : α -> Prop} [m : MeasurableSpace α] :
    MeasurableSpace (Subtype p) :=
  m.comap ((↑) : _ -> α)

section

variable [MeasurableSpace α]

/--
theorem `measurable_subtype_coe` / 定理 `measurable_subtype_coe`

English:
theorem measurable_subtype_coe
  given: {p : α -> Prop}
  statement: Measurable ((↑) : Subtype p -> α)
  proof: MeasurableSpace.le_map_comap

中文:
定理 measurable_subtype_coe
  条件: {p : α -> 命题}
  结论: Measurable ((↑) : Subtype p -> α)
  证明: MeasurableSpace.le_map_comap

Depends on / 依赖: MeasurableSpace, MeasurableSpace.le_map_comap, le_map_comap
-/
theorem measurable_subtype_coe {p : α -> Prop} : Measurable ((↑) : Subtype p -> α) :=
  MeasurableSpace.le_map_comap

/--
Instance `Subtype.instMeasurableSingletonClass` / 实例 `Subtype.instMeasurableSingletonClass`

English:
instance Subtype.instMeasurableSingletonClass
  signature: {p : α -> Prop} [MeasurableSingletonClass α]
  body: ⟨{(x : α)}, measurableSet_singleton (x : α), by
      rw [← image_singleton]; rw [preimage_image_eq _ Subtype.val_injective]⟩

中文:
实例 Subtype.instMeasurableSingletonClass
  签名: {p : α -> 命题} [MeasurableSingletonClass α]
  定义体: ⟨{(x : α)}, measurableSet_singleton (x : α), by
      rw [← image_singleton]; rw [preimage_image_eq _ Subtype.val_injective]⟩

Depends on / 依赖: Subtype, Subtype.val_injective, image_singleton, measurableSet_singleton, preimage_image_eq, val_injective
-/
instance Subtype.instMeasurableSingletonClass {p : α -> Prop} [MeasurableSingletonClass α] :
    MeasurableSingletonClass (Subtype p) where
  measurableSet_singleton x :=
    ⟨{(x : α)}, measurableSet_singleton (x : α), by
      rw [← image_singleton]; rw [preimage_image_eq _ Subtype.val_injective]⟩

end

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}

/--
theorem `MeasurableSet.of_subtype_image` / 定理 `MeasurableSet.of_subtype_image`

English:
theorem MeasurableSet.of_subtype_image
  statement: {s : Set α} {t : Set s}
  proof: ⟨_, h, preimage_image_eq _ Subtype.val_injective⟩

中文:
定理 MeasurableSet.of_subtype_image
  结论: {s : Set α} {t : Set s}
  证明: ⟨_, h, preimage_image_eq _ Subtype.val_injective⟩

Depends on / 依赖: Subtype, Subtype.val_injective, preimage_image_eq, val_injective
-/
theorem MeasurableSet.of_subtype_image {s : Set α} {t : Set s}
    (h : MeasurableSet (Subtype.val '' t)) : MeasurableSet t :=
  ⟨_, h, preimage_image_eq _ Subtype.val_injective⟩

/--
theorem `MeasurableSet.subtype_image` / 定理 `MeasurableSet.subtype_image`

English:
theorem MeasurableSet.subtype_image
  given: {s : Set α} {t : Set s} (hs : MeasurableSet s)
  proof: by
  rintro ⟨u, hu, rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hu

@[fun_prop]

中文:
定理 MeasurableSet.subtype_image
  条件: {s : Set α} {t : Set s} (hs : MeasurableSet s)
  证明: by
  rintro ⟨u, hu, rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hu

@[fun_prop]

Depends on / 依赖: Subtype, Subtype.image_preimage_coe, hs.inter, image_preimage_coe
-/
theorem MeasurableSet.subtype_image {s : Set α} {t : Set s} (hs : MeasurableSet s) :
    MeasurableSet t -> MeasurableSet (((↑) : s -> α) '' t) := by
  rintro ⟨u, hu, rfl⟩
  rw [Subtype.image_preimage_coe]
  exact hs.inter hu

@[fun_prop]
/--
theorem `Measurable.subtype_coe` / 定理 `Measurable.subtype_coe`

English:
theorem Measurable.subtype_coe
  given: {p : β -> Prop} {f : α -> Subtype p} (hf : Measurable f)
  proof: measurable_subtype_coe.comp hf

alias Measurable.subtype_val := Measurable.subtype_coe

@[fun_prop]

中文:
定理 Measurable.subtype_coe
  条件: {p : β -> 命题} {f : α -> Subtype p} (hf : Measurable f)
  证明: measurable_subtype_coe.comp hf

alias Measurable.subtype_val := Measurable.subtype_coe

@[fun_prop]

Depends on / 依赖: measurable_subtype_coe, measurable_subtype_coe.comp
-/
theorem Measurable.subtype_coe {p : β -> Prop} {f : α -> Subtype p} (hf : Measurable f) :
    Measurable fun a : α => (f a : β) :=
  measurable_subtype_coe.comp hf

alias Measurable.subtype_val := Measurable.subtype_coe

@[fun_prop]
/--
theorem `Measurable.subtype_mk` / 定理 `Measurable.subtype_mk`

English:
theorem Measurable.subtype_mk
  given: {p : β -> Prop} {f : α -> β} (hf : Measurable f) {h : forall x, p (f x)}
  proof: fun t ⟨s, hs⟩ =>
  hs.2 ▸ by simp only [← preimage_comp, Function.comp_def, hf hs.1]

@[fun_prop]

中文:
定理 Measurable.subtype_mk
  条件: {p : β -> 命题} {f : α -> β} (hf : Measurable f) {h : 对任意 x, p (f x)}
  证明: fun t ⟨s, hs⟩ =>
  hs.2 ▸ by simp only [← preimage_comp, Function.comp_def, hf hs.1]

@[fun_prop]
-/
theorem Measurable.subtype_mk {p : β -> Prop} {f : α -> β} (hf : Measurable f) {h : forall x, p (f x)} :
    Measurable fun x => (⟨f x, h x⟩ : Subtype p) := fun t ⟨s, hs⟩ =>
  hs.2 ▸ by simp only [← preimage_comp, Function.comp_def, hf hs.1]

@[fun_prop]
/--
theorem `Measurable.codRestrict` / 定理 `Measurable.codRestrict`

English:
theorem Measurable.codRestrict
  statement: {s : Set β} {f : α -> β} (hf : Measurable f)
  proof: hf.subtype_mk

@[fun_prop]

中文:
定理 Measurable.codRestrict
  结论: {s : Set β} {f : α -> β} (hf : Measurable f)
  证明: hf.subtype_mk

@[fun_prop]

Depends on / 依赖: hf.subtype_mk, subtype_mk
-/
theorem Measurable.codRestrict {s : Set β} {f : α -> β} (hf : Measurable f)
    (h : forall y, f y in s) : Measurable (codRestrict f s h) := hf.subtype_mk

@[fun_prop]
/--
theorem `Measurable.rangeFactorization` / 定理 `Measurable.rangeFactorization`

English:
theorem Measurable.rangeFactorization
  given: {f : α -> β} (hf : Measurable f)
  proof: hf.subtype_mk

中文:
定理 Measurable.rangeFactorization
  条件: {f : α -> β} (hf : Measurable f)
  证明: hf.subtype_mk
-/
protected theorem Measurable.rangeFactorization {f : α -> β} (hf : Measurable f) :
    Measurable (rangeFactorization f) :=
  hf.subtype_mk

/--
theorem `Measurable.subtype_map` / 定理 `Measurable.subtype_map`

English:
theorem Measurable.subtype_map
  statement: {f : α -> β} {p : α -> Prop} {q : β -> Prop} (hf : Measurable f)
  proof: (hf.comp measurable_subtype_coe).subtype_mk

中文:
定理 Measurable.subtype_map
  结论: {f : α -> β} {p : α -> 命题} {q : β -> 命题} (hf : Measurable f)
  证明: (hf.comp measurable_subtype_coe).subtype_mk

Depends on / 依赖: hf.comp, measurable_subtype_coe, subtype_mk
-/
theorem Measurable.subtype_map {f : α -> β} {p : α -> Prop} {q : β -> Prop} (hf : Measurable f)
    (hpq : forall x, p x -> q (f x)) : Measurable (Subtype.map f hpq) :=
  (hf.comp measurable_subtype_coe).subtype_mk

/--
theorem `measurable_inclusion` / 定理 `measurable_inclusion`

English:
theorem measurable_inclusion
  given: {s t : Set α} (h : s subseteq t)
  statement: Measurable (inclusion h)
  proof: measurable_id.subtype_map h

中文:
定理 measurable_inclusion
  条件: {s t : Set α} (h : s subseteq t)
  结论: Measurable (inclusion h)
  证明: measurable_id.subtype_map h

Depends on / 依赖: measurable_id, measurable_id.subtype_map, subtype_map
-/
theorem measurable_inclusion {s t : Set α} (h : s subseteq t) : Measurable (inclusion h) :=
  measurable_id.subtype_map h

/--
theorem `MeasurableSet.image_inclusion'` / 定理 `MeasurableSet.image_inclusion'`

English:
theorem MeasurableSet.image_inclusion'
  statement: {s t : Set α} (h : s subseteq t) {u : Set s}
  proof: by
  rcases hu with ⟨u, hu, rfl⟩
  convert! (measurable_subtype_coe hu).inter hs
  ext ⟨x, hx⟩
  simpa [@and_comm _ (_ = x)] using and_comm

中文:
定理 MeasurableSet.image_inclusion'
  结论: {s t : Set α} (h : s subseteq t) {u : Set s}
  证明: by
  rcases hu with ⟨u, hu, rfl⟩
  convert! (measurable_subtype_coe hu).inter hs
  ext ⟨x, hx⟩
  simpa [@and_comm _ (_ = x)] using and_comm

Depends on / 依赖: and_comm, convert, measurable_subtype_coe
-/
theorem MeasurableSet.image_inclusion' {s t : Set α} (h : s subseteq t) {u : Set s}
    (hs : MeasurableSet (Subtype.val ⁻¹' s : Set t)) (hu : MeasurableSet u) :
    MeasurableSet (inclusion h '' u) := by
  rcases hu with ⟨u, hu, rfl⟩
  convert! (measurable_subtype_coe hu).inter hs
  ext ⟨x, hx⟩
  simpa [@and_comm _ (_ = x)] using and_comm

/--
theorem `MeasurableSet.image_inclusion` / 定理 `MeasurableSet.image_inclusion`

English:
theorem MeasurableSet.image_inclusion
  statement: {s t : Set α} (h : s subseteq t) {u : Set s}
  proof: (measurable_subtype_coe hs).image_inclusion' h hu

中文:
定理 MeasurableSet.image_inclusion
  结论: {s t : Set α} (h : s subseteq t) {u : Set s}
  证明: (measurable_subtype_coe hs).image_inclusion' h hu

Depends on / 依赖: image_inclusion, measurable_subtype_coe
-/
theorem MeasurableSet.image_inclusion {s t : Set α} (h : s subseteq t) {u : Set s}
    (hs : MeasurableSet s) (hu : MeasurableSet u) :
    MeasurableSet (inclusion h '' u) :=
  (measurable_subtype_coe hs).image_inclusion' h hu

/--
theorem `MeasurableSet.of_union_cover` / 定理 `MeasurableSet.of_union_cover`

English:
theorem MeasurableSet.of_union_cover
  statement: {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
  proof: by
  convert! (hs.subtype_image hsu).union (ht.subtype_image htu)
  simp [image_preimage_eq_inter_range, ← inter_union_distrib_left, univ_subset_iff.1 h]

中文:
定理 MeasurableSet.of_union_cover
  结论: {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
  证明: by
  convert! (hs.subtype_image hsu).union (ht.subtype_image htu)
  simp [image_preimage_eq_inter_range, ← inter_union_distrib_left, univ_subset_iff.1 h]

Depends on / 依赖: convert, hs.subtype_image, ht.subtype_image, image_preimage_eq_inter_range, inter_union_distrib_left, subtype_image, univ_subset_iff
-/
theorem MeasurableSet.of_union_cover {s t u : Set α} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : univ subseteq s union t) (hsu : MeasurableSet (((↑) : s -> α) ⁻¹' u))
    (htu : MeasurableSet (((↑) : t -> α) ⁻¹' u)) : MeasurableSet u := by
  convert! (hs.subtype_image hsu).union (ht.subtype_image htu)
  simp [image_preimage_eq_inter_range, ← inter_union_distrib_left, univ_subset_iff.1 h]

/--
theorem `measurable_of_measurable_union_cover` / 定理 `measurable_of_measurable_union_cover`

English:
theorem measurable_of_measurable_union_cover
  statement: {f : α -> β} (s t : Set α) (hs : MeasurableSet s)
  proof: fun _u hu =>
  .of_union_cover hs ht h (hc hu) (hd hu)

中文:
定理 measurable_of_measurable_union_cover
  结论: {f : α -> β} (s t : Set α) (hs : MeasurableSet s)
  证明: fun _u hu =>
  .of_union_cover hs ht h (hc hu) (hd hu)
-/
theorem measurable_of_measurable_union_cover {f : α -> β} (s t : Set α) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (h : univ subseteq s union t) (hc : Measurable fun a : s => f a)
    (hd : Measurable fun a : t => f a) : Measurable f := fun _u hu =>
  .of_union_cover hs ht h (hc hu) (hd hu)

/--
theorem `measurable_of_restrict_of_restrict_compl` / 定理 `measurable_of_restrict_of_restrict_compl`

English:
theorem measurable_of_restrict_of_restrict_compl
  statement: {f : α -> β} {s : Set α} (hs : MeasurableSet s)
  proof: measurable_of_measurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁ h₂

中文:
定理 measurable_of_restrict_of_restrict_compl
  结论: {f : α -> β} {s : Set α} (hs : MeasurableSet s)
  证明: measurable_of_measurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁ h₂

Depends on / 依赖: InitialSeg, InitialSeg.refl, hs.compl, measurable_of_measurable_union_cover, union_compl_self
-/
theorem measurable_of_restrict_of_restrict_compl {f : α -> β} {s : Set α} (hs : MeasurableSet s)
    (h₁ : Measurable (s.domRestrict f)) (h₂ : Measurable (sᶜ.domRestrict f)) : Measurable f :=
  measurable_of_measurable_union_cover s sᶜ hs hs.compl (union_compl_self s).ge h₁ h₂

/--
theorem `Measurable.dite` / 定理 `Measurable.dite`

English:
theorem Measurable.dite
  statement: [forall x, Decidable (x in s)] {f : s -> β} (hf : Measurable f)
  proof: measurable_of_restrict_of_restrict_compl hs (by simpa) (by simpa)

中文:
定理 Measurable.dite
  结论: [对任意 x, Decidable (x in s)] {f : s -> β} (hf : Measurable f)
  证明: measurable_of_restrict_of_restrict_compl hs (by simpa) (by simpa)

Depends on / 依赖: measurable_of_restrict_of_restrict_compl
-/
theorem Measurable.dite [forall x, Decidable (x in s)] {f : s -> β} (hf : Measurable f)
    {g : (sᶜ : Set α) -> β} (hg : Measurable g) (hs : MeasurableSet s) :
    Measurable fun x => if hx : x in s then f ⟨x, hx⟩ else g ⟨x, hx⟩ :=
  measurable_of_restrict_of_restrict_compl hs (by simpa) (by simpa)

/--
theorem `measurable_of_measurable_on_compl_finite` / 定理 `measurable_of_measurable_on_compl_finite`

English:
theorem measurable_of_measurable_on_compl_finite
  statement: [MeasurableSingletonClass α] {f : α -> β}
  proof: have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_finite _) hf

中文:
定理 measurable_of_measurable_on_compl_finite
  结论: [MeasurableSingletonClass α] {f : α -> β}
  证明: have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_finite _) hf

Depends on / 依赖: hs.measurableSet, hs.to_subtype, measurableSet, measurable_of_finite, measurable_of_restrict_of_restrict_compl, to_subtype
-/
theorem measurable_of_measurable_on_compl_finite [MeasurableSingletonClass α] {f : α -> β}
    (s : Set α) (hs : s.Finite) (hf : Measurable (sᶜ.domRestrict f)) : Measurable f :=
  have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_finite _) hf

/--
theorem `measurable_of_measurable_on_compl_countable` / 定理 `measurable_of_measurable_on_compl_countable`

English:
theorem measurable_of_measurable_on_compl_countable
  statement: [MeasurableSingletonClass α] {f : α -> β}
  proof: have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_countable _) hf

中文:
定理 measurable_of_measurable_on_compl_countable
  结论: [MeasurableSingletonClass α] {f : α -> β}
  证明: have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_countable _) hf

Depends on / 依赖: hs.measurableSet, hs.to_subtype, measurableSet, measurable_of_countable, measurable_of_restrict_of_restrict_compl, to_subtype
-/
theorem measurable_of_measurable_on_compl_countable [MeasurableSingletonClass α] {f : α -> β}
    (s : Set α) (hs : s.Countable) (hf : Measurable (sᶜ.domRestrict f)) : Measurable f :=
  have := hs.to_subtype
  measurable_of_restrict_of_restrict_compl hs.measurableSet (measurable_of_countable _) hf

/--
theorem `measurable_of_measurable_on_compl_singleton` / 定理 `measurable_of_measurable_on_compl_singleton`

English:
theorem measurable_of_measurable_on_compl_singleton
  statement: [MeasurableSingletonClass α] {f : α -> β} (a : α)
  proof: measurable_of_measurable_on_compl_finite {a} (finite_singleton a) hf

中文:
定理 measurable_of_measurable_on_compl_singleton
  结论: [MeasurableSingletonClass α] {f : α -> β} (a : α)
  证明: measurable_of_measurable_on_compl_finite {a} (finite_singleton a) hf

Depends on / 依赖: finite_singleton, measurable_of_measurable_on_compl_finite
-/
theorem measurable_of_measurable_on_compl_singleton [MeasurableSingletonClass α] {f : α -> β} (a : α)
    (hf : Measurable ({ x | x != a }.domRestrict f)) : Measurable f :=
  measurable_of_measurable_on_compl_finite {a} (finite_singleton a) hf

end Subtype

section Atoms

variable [MeasurableSpace β]

/--
Definition of `measurableAtom` / `measurableAtom` 的定义

English:
definition measurableAtom
  signature: (x : β)
  body: ⋂ (s : Set β) (_h's : x in s) (_hs : MeasurableSet s), s

中文:
定义 measurableAtom
  签名: (x : β)
  定义体: ⋂ (s : Set β) (_h's : x in s) (_hs : MeasurableSet s), s

Depends on / 依赖: MeasurableSet
-/
def measurableAtom (x : β) : Set β :=
  ⋂ (s : Set β) (_h's : x in s) (_hs : MeasurableSet s), s

/--
lemma `mem_measurableAtom_self` / 引理 `mem_measurableAtom_self`

English:
lemma mem_measurableAtom_self
  given: (x : β)
  statement: x in measurableAtom x
  proof: by
  simp +contextual [measurableAtom]

中文:
引理 mem_measurableAtom_self
  条件: (x : β)
  结论: x in measurableAtom x
  证明: by
  simp +contextual [measurableAtom]
-/
@[simp] lemma mem_measurableAtom_self (x : β) : x in measurableAtom x := by
  simp +contextual [measurableAtom]

/--
lemma `mem_of_mem_measurableAtom` / 引理 `mem_of_mem_measurableAtom`

English:
lemma mem_of_mem_measurableAtom
  statement: {x y : β} (h : y in measurableAtom x) {s : Set β}
  proof: by
  simp only [measurableAtom, mem_iInter] at h
  exact h s hxs hs

中文:
引理 mem_of_mem_measurableAtom
  结论: {x y : β} (h : y in measurableAtom x) {s : Set β}
  证明: by
  simp only [measurableAtom, mem_iInter] at h
  exact h s hxs hs

Depends on / 依赖: measurableAtom, mem_iInter
-/
lemma mem_of_mem_measurableAtom {x y : β} (h : y in measurableAtom x) {s : Set β}
    (hs : MeasurableSet s) (hxs : x in s) : y in s := by
  simp only [measurableAtom, mem_iInter] at h
  exact h s hxs hs

/--
lemma `measurableAtom_subset` / 引理 `measurableAtom_subset`

English:
lemma measurableAtom_subset
  given: {s : Set β} {x : β} (hs : MeasurableSet s) (hx : x in s)
  proof: iInter₂_subset_of_subset s hx fun ⦃a⦄ => (by simp [hs])

中文:
引理 measurableAtom_subset
  条件: {s : Set β} {x : β} (hs : MeasurableSet s) (hx : x in s)
  证明: iInter₂_subset_of_subset s hx fun ⦃a⦄ => (by simp [hs])
-/
lemma measurableAtom_subset {s : Set β} {x : β} (hs : MeasurableSet s) (hx : x in s) :
    measurableAtom x subseteq s :=
  iInter₂_subset_of_subset s hx fun ⦃a⦄ => (by simp [hs])

/--
lemma `measurableAtom_of_measurableSingletonClass` / 引理 `measurableAtom_of_measurableSingletonClass`

English:
lemma measurableAtom_of_measurableSingletonClass
  given: [MeasurableSingletonClass β] (x : β)
  proof: Subset.antisymm (measurableAtom_subset (measurableSet_singleton x) rfl) (by simp)

中文:
引理 measurableAtom_of_measurableSingletonClass
  条件: [MeasurableSingletonClass β] (x : β)
  证明: Subset.antisymm (measurableAtom_subset (measurableSet_singleton x) rfl) (by simp)
-/
@[simp] lemma measurableAtom_of_measurableSingletonClass [MeasurableSingletonClass β] (x : β) :
    measurableAtom x = {x} :=
  Subset.antisymm (measurableAtom_subset (measurableSet_singleton x) rfl) (by simp)

/--
lemma `MeasurableSet.measurableAtom_of_countable` / 引理 `MeasurableSet.measurableAtom_of_countable`

English:
lemma MeasurableSet.measurableAtom_of_countable
  given: [Countable β] (x : β)
  proof: by
  have : forall (y : β), y ∉ measurableAtom x -> exists s, x in s ∧ MeasurableSet s ∧ y ∉ s :=
    fun y hy => by simpa [measurableAtom] using hy
  choose! s hs using this
  have : measurableAtom x = ⋂ (y in (measurableAtom x)ᶜ), s y := by
    apply Subset.antisymm
    · intro z hz
      simp onl

中文:
引理 MeasurableSet.measurableAtom_of_countable
  条件: [Countable β] (x : β)
  证明: by
  have : forall (y : β), y ∉ measurableAtom x -> exists s, x in s ∧ MeasurableSet s ∧ y ∉ s :=
    fun y hy => by simpa [measurableAtom] using hy
  choose! s hs using this
  have : measurableAtom x = ⋂ (y in (measurableAtom x)ᶜ), s y := by
    apply Subset.antisymm
    · intro z hz
      simp onl

Depends on / 依赖: MeasurableSet, Subset, Subset.antisymm, antisymm, compl_iInter, compl_subset_compl, exists_prop, measurableAtom, mem_compl_iff, mem_iInter, mem_iUnion, mem_of_mem_measurableAtom
-/
lemma MeasurableSet.measurableAtom_of_countable [Countable β] (x : β) :
    MeasurableSet (measurableAtom x) := by
  have : forall (y : β), y ∉ measurableAtom x -> exists s, x in s ∧ MeasurableSet s ∧ y ∉ s :=
    fun y hy => by simpa [measurableAtom] using hy
  choose! s hs using this
  have : measurableAtom x = ⋂ (y in (measurableAtom x)ᶜ), s y := by
    apply Subset.antisymm
    · intro z hz
      simp only [mem_iInter, mem_compl_iff]
      intro i hi
      exact mem_of_mem_measurableAtom hz (hs i hi).2.1 (hs i hi).1
    · apply compl_subset_compl.1
      intro z hz
      simp only [compl_iInter, mem_iUnion, mem_compl_iff, exists_prop]
      exact ⟨z, hz, (hs z hz).2.2⟩
  rw [this]
  exact MeasurableSet.biInter (to_countable (measurableAtom x)ᶜ) (fun i hi => (hs i hi).2.1)

/--
lemma `measurableAtom_subset_of_mem` / 引理 `measurableAtom_subset_of_mem`

English:
lemma measurableAtom_subset_of_mem
  given: {x y : β} (hx : x in measurableAtom y)
  proof: by
  intro z hz
  simp only [measurableAtom, mem_iInter] at hz hx ⊢
  exact fun s hys hs => hz s (hx s hys hs) hs

中文:
引理 measurableAtom_subset_of_mem
  条件: {x y : β} (hx : x in measurableAtom y)
  证明: by
  intro z hz
  simp only [measurableAtom, mem_iInter] at hz hx ⊢
  exact fun s hys hs => hz s (hx s hys hs) hs

Depends on / 依赖: measurableAtom, mem_iInter
-/
lemma measurableAtom_subset_of_mem {x y : β} (hx : x in measurableAtom y) :
    measurableAtom x subseteq measurableAtom y := by
  intro z hz
  simp only [measurableAtom, mem_iInter] at hz hx ⊢
  exact fun s hys hs => hz s (hx s hys hs) hs

/--
lemma `measurableAtom_eq_of_mem` / 引理 `measurableAtom_eq_of_mem`

English:
lemma measurableAtom_eq_of_mem
  given: {x y : β} (hx : x in measurableAtom y)
  proof: by
  refine subset_antisymm (measurableAtom_subset_of_mem hx) ?_
  by_cases hy : y in measurableAtom x
  · exact measurableAtom_subset_of_mem hy
  exfalso
  simp only [measurableAtom, mem_iInter, not_forall] at hx hy ⊢
  obtain ⟨s, hxs, hs, hys⟩ := hy
  specialize hx sᶜ hys hs.compl
  exact hx hxs

中文:
引理 measurableAtom_eq_of_mem
  条件: {x y : β} (hx : x in measurableAtom y)
  证明: by
  refine subset_antisymm (measurableAtom_subset_of_mem hx) ?_
  by_cases hy : y in measurableAtom x
  · exact measurableAtom_subset_of_mem hy
  exfalso
  simp only [measurableAtom, mem_iInter, not_forall] at hx hy ⊢
  obtain ⟨s, hxs, hs, hys⟩ := hy
  specialize hx sᶜ hys hs.compl
  exact hx hxs

Depends on / 依赖: hs.compl, measurableAtom, measurableAtom_subset_of_mem, mem_iInter, not_forall, specialize, subset_antisymm
-/
lemma measurableAtom_eq_of_mem {x y : β} (hx : x in measurableAtom y) :
    measurableAtom x = measurableAtom y := by
  refine subset_antisymm (measurableAtom_subset_of_mem hx) ?_
  by_cases hy : y in measurableAtom x
  · exact measurableAtom_subset_of_mem hy
  exfalso
  simp only [measurableAtom, mem_iInter, not_forall] at hx hy ⊢
  obtain ⟨s, hxs, hs, hys⟩ := hy
  specialize hx sᶜ hys hs.compl
  exact hx hxs

/--
lemma `disjoint_measurableAtom_of_notMem` / 引理 `disjoint_measurableAtom_of_notMem`

English:
lemma disjoint_measurableAtom_of_notMem
  given: {x y : β} (hx : x ∉ measurableAtom y)
  proof: by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hzx hzy
  have h1 := measurableAtom_eq_of_mem hzx
  have h2 := measurableAtom_eq_of_mem hzy
  rw [← h2]; rw [h1] at hx
  exact hx (mem_measurableAtom_self x)

中文:
引理 disjoint_measurableAtom_of_notMem
  条件: {x y : β} (hx : x ∉ measurableAtom y)
  证明: by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hzx hzy
  have h1 := measurableAtom_eq_of_mem hzx
  have h2 := measurableAtom_eq_of_mem hzy
  rw [← h2]; rw [h1] at hx
  exact hx (mem_measurableAtom_self x)

Depends on / 依赖: Set.disjoint_iff_inter_eq_empty, disjoint_iff_inter_eq_empty, iff_false, measurableAtom_eq_of_mem, mem_empty_iff_false, mem_inter_iff, mem_measurableAtom_self, not_and
-/
lemma disjoint_measurableAtom_of_notMem {x y : β} (hx : x ∉ measurableAtom y) :
    Disjoint (measurableAtom x) (measurableAtom y) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext z
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hzx hzy
  have h1 := measurableAtom_eq_of_mem hzx
  have h2 := measurableAtom_eq_of_mem hzy
  rw [← h2]; rw [h1] at hx
  exact hx (mem_measurableAtom_self x)

end Atoms

section Prod

/-- A `MeasurableSpace` structure on the product of two measurable spaces. -/
@[instance_reducible]
/--
Definition of `MeasurableSpace.prod` / `MeasurableSpace.prod` 的定义

English:
definition MeasurableSpace.prod
  signature: {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β)
  body: m₁.comap Prod.fst ⊔ m₂.comap Prod.snd

中文:
定义 MeasurableSpace.prod
  签名: {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β)
  定义体: m₁.comap Prod.fst ⊔ m₂.comap Prod.snd

Depends on / 依赖: Prod.fst, Prod.snd
-/
def MeasurableSpace.prod {α β} (m₁ : MeasurableSpace α) (m₂ : MeasurableSpace β) :
    MeasurableSpace (α × β) :=
  m₁.comap Prod.fst ⊔ m₂.comap Prod.snd

/--
Instance `Prod.instMeasurableSpace` / 实例 `Prod.instMeasurableSpace`

English:
instance Prod.instMeasurableSpace
  signature: {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β]
  body: m₁.prod m₂

中文:
实例 Prod.instMeasurableSpace
  签名: {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β]
  定义体: m₁.prod m₂
-/
instance Prod.instMeasurableSpace {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] :
    MeasurableSpace (α × β) :=
  m₁.prod m₂

/--
theorem `measurable_fst` / 定理 `measurable_fst`

English:
theorem measurable_fst
  given: {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  proof: Measurable.of_comap_le le_sup_left

中文:
定理 measurable_fst
  条件: {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  证明: Measurable.of_comap_le le_sup_left

Depends on / 依赖: Measurable, Measurable.of_comap_le, le_sup_left, of_comap_le
-/
theorem measurable_fst {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    Measurable (Prod.fst : α × β -> α) :=
  Measurable.of_comap_le le_sup_left

/--
theorem `measurable_snd` / 定理 `measurable_snd`

English:
theorem measurable_snd
  given: {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  proof: Measurable.of_comap_le le_sup_right

中文:
定理 measurable_snd
  条件: {_ : MeasurableSpace α} {_ : MeasurableSpace β}
  证明: Measurable.of_comap_le le_sup_right

Depends on / 依赖: Measurable, Measurable.of_comap_le, le_sup_right, of_comap_le
-/
theorem measurable_snd {_ : MeasurableSpace α} {_ : MeasurableSpace β} :
    Measurable (Prod.snd : α × β -> β) :=
  Measurable.of_comap_le le_sup_right

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}

@[fun_prop]
/--
theorem `Measurable.fst` / 定理 `Measurable.fst`

English:
theorem Measurable.fst
  given: {f : α -> β × γ} (hf : Measurable f)
  statement: Measurable fun a : α => (f a).1
  proof: measurable_fst.comp hf

@[fun_prop]

中文:
定理 Measurable.fst
  条件: {f : α -> β × γ} (hf : Measurable f)
  结论: Measurable fun a : α => (f a).1
  证明: measurable_fst.comp hf

@[fun_prop]

Depends on / 依赖: measurable_fst, measurable_fst.comp
-/
theorem Measurable.fst {f : α -> β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).1 :=
  measurable_fst.comp hf

@[fun_prop]
/--
theorem `Measurable.snd` / 定理 `Measurable.snd`

English:
theorem Measurable.snd
  given: {f : α -> β × γ} (hf : Measurable f)
  statement: Measurable fun a : α => (f a).2
  proof: measurable_snd.comp hf

中文:
定理 Measurable.snd
  条件: {f : α -> β × γ} (hf : Measurable f)
  结论: Measurable fun a : α => (f a).2
  证明: measurable_snd.comp hf

Depends on / 依赖: measurable_snd, measurable_snd.comp
-/
theorem Measurable.snd {f : α -> β × γ} (hf : Measurable f) : Measurable fun a : α => (f a).2 :=
  measurable_snd.comp hf

/--
theorem `Measurable.prod` / 定理 `Measurable.prod`

English:
theorem Measurable.prod
  statement: {f : α -> β × γ} (hf₁ : Measurable fun a => (f a).1)
  proof: Measurable.of_le_map
    sup_le
      (by
        rw [MeasurableSpace.comap_le_iff_le_map]; rw [MeasurableSpace.map_comp]
        exact hf₁)
      (by
        rw [MeasurableSpace.comap_le_iff_le_map]; rw [MeasurableSpace.map_comp]
        exact hf₂)

@[fun_prop]

中文:
定理 Measurable.prod
  结论: {f : α -> β × γ} (hf₁ : Measurable fun a => (f a).1)
  证明: Measurable.of_le_map
    sup_le
      (by
        rw [MeasurableSpace.comap_le_iff_le_map]; rw [MeasurableSpace.map_comp]
        exact hf₁)
      (by
        rw [MeasurableSpace.comap_le_iff_le_map]; rw [MeasurableSpace.map_comp]
        exact hf₂)

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.of_le_map, MeasurableSpace, MeasurableSpace.comap_le_iff_le_map, MeasurableSpace.map_comp, comap_le_iff_le_map, map_comp, of_le_map, sup_le
-/
theorem Measurable.prod {f : α -> β × γ} (hf₁ : Measurable fun a => (f a).1)
    (hf₂ : Measurable fun a => (f a).2) : Measurable f :=
Measurable.of_le_map
    sup_le
      (by
        rw [MeasurableSpace.comap_le_iff_le_map]; rw [MeasurableSpace.map_comp]
        exact hf₁)
      (by
        rw [MeasurableSpace.comap_le_iff_le_map]; rw [MeasurableSpace.map_comp]
        exact hf₂)

@[fun_prop]
/--
theorem `Measurable.prodMk` / 定理 `Measurable.prodMk`

English:
theorem Measurable.prodMk
  statement: {β γ} {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {f : α -> β}
  proof: Measurable.prod hf hg

@[fun_prop]

中文:
定理 Measurable.prodMk
  结论: {β γ} {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {f : α -> β}
  证明: Measurable.prod hf hg

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.prod
-/
theorem Measurable.prodMk {β γ} {_ : MeasurableSpace β} {_ : MeasurableSpace γ} {f : α -> β}
    {g : α -> γ} (hf : Measurable f) (hg : Measurable g) : Measurable fun a : α => (f a, g a) :=
  Measurable.prod hf hg

@[fun_prop]
/--
theorem `Measurable.prodMap` / 定理 `Measurable.prodMap`

English:
theorem Measurable.prodMap
  statement: [MeasurableSpace δ] {f : α -> β} {g : γ -> δ} (hf : Measurable f)
  proof: (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)

中文:
定理 Measurable.prodMap
  结论: [MeasurableSpace δ] {f : α -> β} {g : γ -> δ} (hf : Measurable f)
  证明: (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)

Depends on / 依赖: hf.comp, hg.comp, measurable_fst, measurable_snd, prodMk
-/
theorem Measurable.prodMap [MeasurableSpace δ] {f : α -> β} {g : γ -> δ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Prod.map f g) :=
  (hf.comp measurable_fst).prodMk (hg.comp measurable_snd)

/--
theorem `measurable_prodMk_left` / 定理 `measurable_prodMk_left`

English:
theorem measurable_prodMk_left
  given: {x : α}
  statement: Measurable (@Prod.mk _ β x)
  proof: measurable_const.prodMk measurable_id

中文:
定理 measurable_prodMk_left
  条件: {x : α}
  结论: Measurable (@Prod.mk _ β x)
  证明: measurable_const.prodMk measurable_id

Depends on / 依赖: measurable_const, measurable_const.prodMk, measurable_id, prodMk
-/
theorem measurable_prodMk_left {x : α} : Measurable (@Prod.mk _ β x) :=
  measurable_const.prodMk measurable_id

/--
theorem `measurable_prodMk_right` / 定理 `measurable_prodMk_right`

English:
theorem measurable_prodMk_right
  given: {y : β}
  statement: Measurable fun x : α => (x, y)
  proof: measurable_id.prodMk measurable_const

@[fun_prop]

中文:
定理 measurable_prodMk_right
  条件: {y : β}
  结论: Measurable fun x : α => (x, y)
  证明: measurable_id.prodMk measurable_const

@[fun_prop]

Depends on / 依赖: measurable_const, measurable_id, measurable_id.prodMk, prodMk
-/
theorem measurable_prodMk_right {y : β} : Measurable fun x : α => (x, y) :=
  measurable_id.prodMk measurable_const

@[fun_prop]
/--
theorem `measurable_diag` / 定理 `measurable_diag`

English:
theorem measurable_diag
  statement: @Measurable α (α × α) m (m.prod m) Function.diag
  proof: measurable_id.prodMk measurable_id

中文:
定理 measurable_diag
  结论: @Measurable α (α × α) m (m.prod m) Function.diag
  证明: measurable_id.prodMk measurable_id

Depends on / 依赖: measurable_id, measurable_id.prodMk, prodMk
-/
theorem measurable_diag : @Measurable α (α × α) m (m.prod m) Function.diag :=
  measurable_id.prodMk measurable_id

/--
theorem `measurable_diag'` / 定理 `measurable_diag'`

English:
theorem measurable_diag'
  given: {m'} (h : m' <= m)
  statement: @Measurable α (α × α) m (m.prod m') Function.diag
  proof: measurable_id.prodMk (measurable_id'' h)

中文:
定理 measurable_diag'
  条件: {m'} (h : m' <= m)
  结论: @Measurable α (α × α) m (m.prod m') Function.diag
  证明: measurable_id.prodMk (measurable_id'' h)

Depends on / 依赖: measurable_id, measurable_id.prodMk, prodMk
-/
theorem measurable_diag' {m'} (h : m' <= m) : @Measurable α (α × α) m (m.prod m') Function.diag :=
  measurable_id.prodMk (measurable_id'' h)

/--
theorem `Measurable.of_uncurry_left` / 定理 `Measurable.of_uncurry_left`

English:
theorem Measurable.of_uncurry_left
  given: {f : α -> β -> γ} (hf : Measurable (uncurry f)) {x : α}
  proof: hf.comp measurable_prodMk_left

中文:
定理 Measurable.of_uncurry_left
  条件: {f : α -> β -> γ} (hf : Measurable (uncurry f)) {x : α}
  证明: hf.comp measurable_prodMk_left

Depends on / 依赖: hf.comp, measurable_prodMk_left
-/
theorem Measurable.of_uncurry_left {f : α -> β -> γ} (hf : Measurable (uncurry f)) {x : α} :
    Measurable (f x) :=
  hf.comp measurable_prodMk_left

/--
theorem `Measurable.of_uncurry_right` / 定理 `Measurable.of_uncurry_right`

English:
theorem Measurable.of_uncurry_right
  given: {f : α -> β -> γ} (hf : Measurable (uncurry f)) {y : β}
  proof: hf.comp measurable_prodMk_right

中文:
定理 Measurable.of_uncurry_right
  条件: {f : α -> β -> γ} (hf : Measurable (uncurry f)) {y : β}
  证明: hf.comp measurable_prodMk_right

Depends on / 依赖: hf.comp, measurable_prodMk_right
-/
theorem Measurable.of_uncurry_right {f : α -> β -> γ} (hf : Measurable (uncurry f)) {y : β} :
    Measurable fun x => f x y :=
  hf.comp measurable_prodMk_right

/--
theorem `measurable_fun_prod` / 定理 `measurable_fun_prod`

English:
theorem measurable_fun_prod
  given: {f : α -> β × γ}
  proof: ⟨fun hf => ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, fun h => Measurable.prod h.1 h.2⟩

@[fun_prop]

中文:
定理 measurable_fun_prod
  条件: {f : α -> β × γ}
  证明: ⟨fun hf => ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, fun h => Measurable.prod h.1 h.2⟩

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.prod, measurable_fst, measurable_fst.comp, measurable_snd, measurable_snd.comp
-/
theorem measurable_fun_prod {f : α -> β × γ} :
    Measurable f ↔ (Measurable fun a => (f a).1) ∧ Measurable fun a => (f a).2 :=
  ⟨fun hf => ⟨measurable_fst.comp hf, measurable_snd.comp hf⟩, fun h => Measurable.prod h.1 h.2⟩

@[fun_prop]
/--
theorem `measurable_swap` / 定理 `measurable_swap`

English:
theorem measurable_swap
  statement: Measurable (Prod.swap : α × β -> β × α)
  proof: Measurable.prod measurable_snd measurable_fst

中文:
定理 measurable_swap
  结论: Measurable (Prod.swap : α × β -> β × α)
  证明: Measurable.prod measurable_snd measurable_fst

Depends on / 依赖: Measurable, Measurable.prod, measurable_fst, measurable_snd
-/
theorem measurable_swap : Measurable (Prod.swap : α × β -> β × α) :=
  Measurable.prod measurable_snd measurable_fst

/--
theorem `measurable_swap_iff` / 定理 `measurable_swap_iff`

English:
theorem measurable_swap_iff
  given: {_ : MeasurableSpace γ} {f : α × β -> γ}
  proof: ⟨fun hf => hf.comp measurable_swap, fun hf => hf.comp measurable_swap⟩

@[measurability]

中文:
定理 measurable_swap_iff
  条件: {_ : MeasurableSpace γ} {f : α × β -> γ}
  证明: ⟨fun hf => hf.comp measurable_swap, fun hf => hf.comp measurable_swap⟩

@[measurability]

Depends on / 依赖: hf.comp, measurable_swap
-/
theorem measurable_swap_iff {_ : MeasurableSpace γ} {f : α × β -> γ} :
    Measurable (f ∘ Prod.swap) ↔ Measurable f :=
  ⟨fun hf => hf.comp measurable_swap, fun hf => hf.comp measurable_swap⟩

@[measurability]
/--
theorem `MeasurableSet.prod` / 定理 `MeasurableSet.prod`

English:
theorem MeasurableSet.prod
  statement: {s : Set α} {t : Set β} (hs : MeasurableSet s)
  proof: MeasurableSet.inter (measurable_fst hs) (measurable_snd ht)

中文:
定理 MeasurableSet.prod
  结论: {s : Set α} {t : Set β} (hs : MeasurableSet s)
  证明: MeasurableSet.inter (measurable_fst hs) (measurable_snd ht)
-/
protected theorem MeasurableSet.prod {s : Set α} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : MeasurableSet (s ×ˢ t) :=
  MeasurableSet.inter (measurable_fst hs) (measurable_snd ht)

/--
theorem `measurableSet_prod_of_nonempty` / 定理 `measurableSet_prod_of_nonempty`

English:
theorem measurableSet_prod_of_nonempty
  given: {s : Set α} {t : Set β} (h : (s ×ˢ t).Nonempty)
  proof: by
  rcases h with ⟨⟨x, y⟩, hx, hy⟩
  refine ⟨fun hst => ?_, fun h => h.1.prod h.2⟩
  have : MeasurableSet ((fun x => (x, y)) ⁻¹' s ×ˢ t) := measurable_prodMk_right hst
  have : MeasurableSet (Prod.mk x ⁻¹' s ×ˢ t) := measurable_prodMk_left hst
  simp_all

中文:
定理 measurableSet_prod_of_nonempty
  条件: {s : Set α} {t : Set β} (h : (s ×ˢ t).Nonempty)
  证明: by
  rcases h with ⟨⟨x, y⟩, hx, hy⟩
  refine ⟨fun hst => ?_, fun h => h.1.prod h.2⟩
  have : MeasurableSet ((fun x => (x, y)) ⁻¹' s ×ˢ t) := measurable_prodMk_right hst
  have : MeasurableSet (Prod.mk x ⁻¹' s ×ˢ t) := measurable_prodMk_left hst
  simp_all

Depends on / 依赖: MeasurableSet, Prod.mk, measurable_prodMk_left, measurable_prodMk_right
-/
theorem measurableSet_prod_of_nonempty {s : Set α} {t : Set β} (h : (s ×ˢ t).Nonempty) :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t := by
  rcases h with ⟨⟨x, y⟩, hx, hy⟩
  refine ⟨fun hst => ?_, fun h => h.1.prod h.2⟩
  have : MeasurableSet ((fun x => (x, y)) ⁻¹' s ×ˢ t) := measurable_prodMk_right hst
  have : MeasurableSet (Prod.mk x ⁻¹' s ×ˢ t) := measurable_prodMk_left hst
  simp_all

/--
theorem `measurableSet_prod` / 定理 `measurableSet_prod`

English:
theorem measurableSet_prod
  given: {s : Set α} {t : Set β}
  proof: by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.mp h]
  · simp [← not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurableSet_prod_of_nonempty h]

中文:
定理 measurableSet_prod
  条件: {s : Set α} {t : Set β}
  证明: by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.mp h]
  · simp [← not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurableSet_prod_of_nonempty h]

Depends on / 依赖: eq_empty_or_nonempty, f.irrefl, irrefl, measurableSet_prod_of_nonempty, not_nonempty_iff_eq_empty, prod_eq_empty_iff, prod_eq_empty_iff.mp, prod_nonempty_iff, prod_nonempty_iff.mp
-/
theorem measurableSet_prod {s : Set α} {t : Set β} :
    MeasurableSet (s ×ˢ t) ↔ MeasurableSet s ∧ MeasurableSet t ∨ s = ∅ ∨ t = ∅ := by
  rcases (s ×ˢ t).eq_empty_or_nonempty with h | h
  · simp [h, prod_eq_empty_iff.mp h]
  · simp [← not_nonempty_iff_eq_empty, prod_nonempty_iff.mp h, measurableSet_prod_of_nonempty h]

/--
theorem `measurableSet_swap_iff` / 定理 `measurableSet_swap_iff`

English:
theorem measurableSet_swap_iff
  given: {s : Set (α × β)}
  proof: ⟨fun hs => measurable_swap hs, fun hs => measurable_swap hs⟩

中文:
定理 measurableSet_swap_iff
  条件: {s : Set (α × β)}
  证明: ⟨fun hs => measurable_swap hs, fun hs => measurable_swap hs⟩

Depends on / 依赖: measurable_swap
-/
theorem measurableSet_swap_iff {s : Set (α × β)} :
    MeasurableSet (Prod.swap ⁻¹' s) ↔ MeasurableSet s :=
  ⟨fun hs => measurable_swap hs, fun hs => measurable_swap hs⟩

/--
Instance `Prod.instMeasurableSingletonClass` / 实例 `Prod.instMeasurableSingletonClass`

English:
instance Prod.instMeasurableSingletonClass
  body: ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ .prod (.singleton a) (.singleton b)⟩

中文:
实例 Prod.instMeasurableSingletonClass
  定义体: ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ .prod (.singleton a) (.singleton b)⟩

Depends on / 依赖: singleton, singleton_prod_singleton
-/
instance Prod.instMeasurableSingletonClass
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] :
    MeasurableSingletonClass (α × β) :=
  ⟨fun ⟨a, b⟩ => @singleton_prod_singleton _ _ a b ▸ .prod (.singleton a) (.singleton b)⟩

/--
theorem `measurable_from_prod_countable_left'` / 定理 `measurable_from_prod_countable_left'`

English:
theorem measurable_from_prod_countable_left'
  statement: [Countable β] {f : α × β -> γ}
  proof: fun s hs => by
  have : f ⁻¹' s = ⋃ y, ((fun x => f (x, y)) ⁻¹' s) ×ˢ (measurableAtom y : Set β) := by
    ext1 ⟨x, y⟩
    simp only [mem_preimage, mem_iUnion, mem_prod]
    refine ⟨fun h => ⟨y, h, mem_measurableAtom_self y⟩, ?_⟩
    rintro ⟨y', hy's, hy'⟩
    rwa [h'f y' y x hy']
  rw [this]
  exac

中文:
定理 measurable_from_prod_countable_left'
  结论: [Countable β] {f : α × β -> γ}
  证明: fun s hs => by
  have : f ⁻¹' s = ⋃ y, ((fun x => f (x, y)) ⁻¹' s) ×ˢ (measurableAtom y : Set β) := by
    ext1 ⟨x, y⟩
    simp only [mem_preimage, mem_iUnion, mem_prod]
    refine ⟨fun h => ⟨y, h, mem_measurableAtom_self y⟩, ?_⟩
    rintro ⟨y', hy's, hy'⟩
    rwa [h'f y' y x hy']
  rw [this]
  exac

Depends on / 依赖: iUnion, measurableAtom, measurableAtom_of_countable, mem_iUnion, mem_measurableAtom_self, mem_preimage, mem_prod
-/
theorem measurable_from_prod_countable_left' [Countable β] {f : α × β -> γ}
    (hf : forall y, Measurable fun x => f (x, y))
    (h'f : forall y y' x, y' in measurableAtom y -> f (x, y') = f (x, y)) : Measurable f := fun s hs => by
  have : f ⁻¹' s = ⋃ y, ((fun x => f (x, y)) ⁻¹' s) ×ˢ (measurableAtom y : Set β) := by
    ext1 ⟨x, y⟩
    simp only [mem_preimage, mem_iUnion, mem_prod]
    refine ⟨fun h => ⟨y, h, mem_measurableAtom_self y⟩, ?_⟩
    rintro ⟨y', hy's, hy'⟩
    rwa [h'f y' y x hy']
  rw [this]
  exact .iUnion (fun y => (hf y hs).prod (.measurableAtom_of_countable y))

/--
lemma `measurable_from_prod_countable_right'` / 引理 `measurable_from_prod_countable_right'`

English:
lemma measurable_from_prod_countable_right'
  statement: [Countable α] {f : α × β -> γ}
  proof: by
  change Measurable ((fun p => f (p.2, p.1)) ∘ Prod.swap)
  exact (measurable_from_prod_countable_left' hf h'f).comp measurable_swap

中文:
引理 measurable_from_prod_countable_right'
  结论: [Countable α] {f : α × β -> γ}
  证明: by
  change Measurable ((fun p => f (p.2, p.1)) ∘ Prod.swap)
  exact (measurable_from_prod_countable_left' hf h'f).comp measurable_swap

Depends on / 依赖: Measurable, Prod.swap, measurable_from_prod_countable_left, measurable_swap
-/
lemma measurable_from_prod_countable_right' [Countable α] {f : α × β -> γ}
    (hf : forall x, Measurable fun y => f (x, y))
    (h'f : forall x x' y, x' in measurableAtom x -> f (x', y) = f (x, y)) : Measurable f := by
  change Measurable ((fun p => f (p.2, p.1)) ∘ Prod.swap)
  exact (measurable_from_prod_countable_left' hf h'f).comp measurable_swap

/--
theorem `measurable_from_prod_countable_left` / 定理 `measurable_from_prod_countable_left`

English:
theorem measurable_from_prod_countable_left
  statement: [Countable β] [MeasurableSingletonClass β]
  proof: measurable_from_prod_countable_left' hf (by simp +contextual)

中文:
定理 measurable_from_prod_countable_left
  结论: [Countable β] [MeasurableSingletonClass β]
  证明: measurable_from_prod_countable_left' hf (by simp +contextual)

Depends on / 依赖: contextual, measurable_from_prod_countable_left
-/
theorem measurable_from_prod_countable_left [Countable β] [MeasurableSingletonClass β]
    {f : α × β -> γ} (hf : forall y, Measurable fun x => f (x, y)) :
    Measurable f :=
  measurable_from_prod_countable_left' hf (by simp +contextual)

/--
lemma `measurable_from_prod_countable_right` / 引理 `measurable_from_prod_countable_right`

English:
lemma measurable_from_prod_countable_right
  statement: [Countable α] [MeasurableSingletonClass α]
  proof: measurable_from_prod_countable_right' hf (by simp +contextual)

中文:
引理 measurable_from_prod_countable_right
  结论: [Countable α] [MeasurableSingletonClass α]
  证明: measurable_from_prod_countable_right' hf (by simp +contextual)

Depends on / 依赖: contextual, measurable_from_prod_countable_right
-/
lemma measurable_from_prod_countable_right [Countable α] [MeasurableSingletonClass α]
    {f : α × β -> γ} (hf : forall x, Measurable fun y => f (x, y)) : Measurable f :=
  measurable_from_prod_countable_right' hf (by simp +contextual)

/--
theorem `Measurable.find` / 定理 `Measurable.find`

English:
theorem Measurable.find
  statement: {_ : MeasurableSpace α} {f : Nat -> α -> β} {p : Nat -> α -> Prop}
  proof: have : Measurable fun p : α × Nat => f p.2 p.1 := measurable_from_prod_countable_left fun n => hf n
  this.comp (Measurable.prodMk measurable_id (measurable_find h hp))

中文:
定理 Measurable.find
  结论: {_ : MeasurableSpace α} {f : 自然数 -> α -> β} {p : 自然数 -> α -> 命题}
  证明: have : Measurable fun p : α × Nat => f p.2 p.1 := measurable_from_prod_countable_left fun n => hf n
  this.comp (Measurable.prodMk measurable_id (measurable_find h hp))

Depends on / 依赖: Measurable, Measurable.prodMk, measurable_find, measurable_from_prod_countable_left, measurable_id, prodMk, this.comp
-/
theorem Measurable.find {_ : MeasurableSpace α} {f : Nat -> α -> β} {p : Nat -> α -> Prop}
    [forall n, DecidablePred (p n)] (hf : forall n, Measurable (f n)) (hp : forall n, MeasurableSet { x | p n x })
    (h : forall x, exists n, p n x) : Measurable fun x => f (Nat.find (h x)) x :=
  have : Measurable fun p : α × Nat => f p.2 p.1 := measurable_from_prod_countable_left fun n => hf n
  this.comp (Measurable.prodMk measurable_id (measurable_find h hp))

/--
theorem `measurable_iUnionLift` / 定理 `measurable_iUnionLift`

English:
theorem measurable_iUnionLift
  statement: [Countable ι] {t : ι -> Set α} {f : forall i, t i -> β}
  proof: fun s hs => by
  rw [preimage_iUnionLift]
  exact .preimage (.iUnion fun i => .image_inclusion _ (htm _) (hfm i hs)) (measurable_inclusion _)

中文:
定理 measurable_iUnionLift
  结论: [Countable ι] {t : ι -> Set α} {f : 对任意 i, t i -> β}
  证明: fun s hs => by
  rw [preimage_iUnionLift]
  exact .preimage (.iUnion fun i => .image_inclusion _ (htm _) (hfm i hs)) (measurable_inclusion _)

Depends on / 依赖: iUnion, image_inclusion, measurable_inclusion, preimage, preimage_iUnionLift
-/
theorem measurable_iUnionLift [Countable ι] {t : ι -> Set α} {f : forall i, t i -> β}
    (htf : forall (i j) (x : α) (hxi : x in t i) (hxj : x in t j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    {T : Set α} (hT : T subseteq ⋃ i, t i) (htm : forall i, MeasurableSet (t i)) (hfm : forall i, Measurable (f i)) :
    Measurable (iUnionLift t f htf T hT) := fun s hs => by
  rw [preimage_iUnionLift]
  exact .preimage (.iUnion fun i => .image_inclusion _ (htm _) (hfm i hs)) (measurable_inclusion _)

/--
theorem `measurable_liftCover` / 定理 `measurable_liftCover`

English:
theorem measurable_liftCover
  statement: [Countable ι] (t : ι -> Set α) (htm : forall i, MeasurableSet (t i))
  proof: fun s hs => by
  rw [preimage_liftCover]
exact .iUnion fun i => .subtype_image (htm i) hfm i hs

中文:
定理 measurable_liftCover
  结论: [Countable ι] (t : ι -> Set α) (htm : 对任意 i, MeasurableSet (t i))
  证明: fun s hs => by
  rw [preimage_liftCover]
exact .iUnion fun i => .subtype_image (htm i) hfm i hs

Depends on / 依赖: iUnion, preimage_liftCover, subtype_image
-/
theorem measurable_liftCover [Countable ι] (t : ι -> Set α) (htm : forall i, MeasurableSet (t i))
    (f : forall i, t i -> β) (hfm : forall i, Measurable (f i))
    (hf : forall (i j) (x : α) (hxi : x in t i) (hxj : x in t j), f i ⟨x, hxi⟩ = f j ⟨x, hxj⟩)
    (htU : ⋃ i, t i = univ) :
    Measurable (liftCover t f hf htU) := fun s hs => by
  rw [preimage_liftCover]
exact .iUnion fun i => .subtype_image (htm i) hfm i hs

/--
theorem `exists_measurable_piecewise` / 定理 `exists_measurable_piecewise`

English:
theorem exists_measurable_piecewise
  statement: {ι} [Countable ι] [Nonempty ι] (t : ι -> Set α)
  proof: by
  inhabit ι
  set g' : (i : ι) -> t i -> β := fun i => g i ∘ (↑)
  -- see https://github.com/leanprover-community/mathlib4/issues/2184
  have ht' : forall (i j) (x : α) (hxi : x in t i) (hxj : x in t j), g' i ⟨x, hxi⟩ = g' j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases eq_or_ne i j with rfl 

中文:
定理 exists_measurable_piecewise
  结论: {ι} [Countable ι] [Nonempty ι] (t : ι -> Set α)
  证明: by
  inhabit ι
  set g' : (i : ι) -> t i -> β := fun i => g i ∘ (↑)
  -- see https://github.com/leanprover-community/mathlib4/issues/2184
  have ht' : forall (i j) (x : α) (hxi : x in t i) (hxj : x in t j), g' i ⟨x, hxi⟩ = g' j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases eq_or_ne i j with rfl 

Depends on / 依赖: inhabit
-/
theorem exists_measurable_piecewise {ι} [Countable ι] [Nonempty ι] (t : ι -> Set α)
    (t_meas : forall n, MeasurableSet (t n)) (g : ι -> α -> β) (hg : forall n, Measurable (g n))
    (ht : Pairwise fun i j => EqOn (g i) (g j) (t i inter t j)) :
    exists f : α -> β, Measurable f ∧ forall n, EqOn f (g n) (t n) := by
  inhabit ι
  set g' : (i : ι) -> t i -> β := fun i => g i ∘ (↑)
  -- see https://github.com/leanprover-community/mathlib4/issues/2184
  have ht' : forall (i j) (x : α) (hxi : x in t i) (hxj : x in t j), g' i ⟨x, hxi⟩ = g' j ⟨x, hxj⟩ := by
    intro i j x hxi hxj
    rcases eq_or_ne i j with rfl | hij
    · rfl
    · exact ht hij ⟨hxi, hxj⟩
  set f : (⋃ i, t i) -> β := iUnionLift t g' ht' _ Subset.rfl
  have hfm : Measurable f := measurable_iUnionLift _ _ t_meas
    (fun i => (hg i).comp measurable_subtype_coe)
  classical
    refine ⟨fun x => if hx : x in ⋃ i, t i then f ⟨x, hx⟩ else g default x,
      hfm.dite ((hg default).comp measurable_subtype_coe) (.iUnion t_meas), fun i x hx => ?_⟩
    simp only [dif_pos (mem_iUnion.2 ⟨i, hx⟩)]
    exact iUnionLift_of_mem ⟨x, mem_iUnion.2 ⟨i, hx⟩⟩ hx

end Prod

section Pi

variable {X : δ -> Type*} [MeasurableSpace α]

/--
Instance `MeasurableSpace.pi` / 实例 `MeasurableSpace.pi`

English:
instance MeasurableSpace.pi
  signature: [m : forall a, MeasurableSpace (X a)]
  body: ⨆ a, (m a).comap fun b => b a

中文:
实例 MeasurableSpace.pi
  签名: [m : 对任意 a, MeasurableSpace (X a)]
  定义体: ⨆ a, (m a).comap fun b => b a
-/
instance MeasurableSpace.pi [m : forall a, MeasurableSpace (X a)] : MeasurableSpace (forall a, X a) :=
  ⨆ a, (m a).comap fun b => b a

variable [forall a, MeasurableSpace (X a)] [MeasurableSpace γ]

/--
theorem `measurable_pi_iff` / 定理 `measurable_pi_iff`

English:
theorem measurable_pi_iff
  given: {g : α -> forall a, X a}
  statement: Measurable g ↔ forall a, Measurable fun x => g x a
  proof: by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]

中文:
定理 measurable_pi_iff
  条件: {g : α -> 对任意 a, X a}
  结论: Measurable g ↔ 对任意 a, Measurable fun x => g x a
  证明: by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]

Depends on / 依赖: Function, Function.comp_def, MeasurableSpace, MeasurableSpace.comap_comp, MeasurableSpace.comap_iSup, MeasurableSpace.pi, comap_comp, comap_iSup, comp_def, iSup_le_iff, measurable_iff_comap_le, simp_rw
-/
theorem measurable_pi_iff {g : α -> forall a, X a} : Measurable g ↔ forall a, Measurable fun x => g x a := by
  simp_rw [measurable_iff_comap_le, MeasurableSpace.pi, MeasurableSpace.comap_iSup,
    MeasurableSpace.comap_comp, Function.comp_def, iSup_le_iff]

@[fun_prop]
/--
theorem `measurable_pi_apply` / 定理 `measurable_pi_apply`

English:
theorem measurable_pi_apply
  given: (a : δ)
  statement: Measurable fun f : forall a, X a => f a
  proof: measurable_pi_iff.1 measurable_id a

中文:
定理 measurable_pi_apply
  条件: (a : δ)
  结论: Measurable fun f : 对任意 a, X a => f a
  证明: measurable_pi_iff.1 measurable_id a

Depends on / 依赖: measurable_id, measurable_pi_iff
-/
theorem measurable_pi_apply (a : δ) : Measurable fun f : forall a, X a => f a :=
  measurable_pi_iff.1 measurable_id a

/--
theorem `MeasurableSpace.comap_le_comap_pi` / 定理 `MeasurableSpace.comap_le_comap_pi`

English:
theorem MeasurableSpace.comap_le_comap_pi
  given: {g : (a : δ) -> β -> X a} (a : δ)
  proof: by
simpa only [pi, comap_iSup] using le_iSup_of_le a by measurability

中文:
定理 MeasurableSpace.comap_le_comap_pi
  条件: {g : (a : δ) -> β -> X a} (a : δ)
  证明: by
simpa only [pi, comap_iSup] using le_iSup_of_le a by measurability

Depends on / 依赖: comap_iSup, le_iSup_of_le, measurability
-/
theorem MeasurableSpace.comap_le_comap_pi {g : (a : δ) -> β -> X a} (a : δ) :
    .comap (g a) inferInstance <= pi.comap (fun b c => g c b) := by
simpa only [pi, comap_iSup] using le_iSup_of_le a by measurability

/--
theorem `Measurable.eval` / 定理 `Measurable.eval`

English:
theorem Measurable.eval
  given: {a : δ} {g : α -> forall a, X a} (hg : Measurable g)
  proof: (measurable_pi_apply a).comp hg

@[fun_prop]

中文:
定理 Measurable.eval
  条件: {a : δ} {g : α -> 对任意 a, X a} (hg : Measurable g)
  证明: (measurable_pi_apply a).comp hg

@[fun_prop]

Depends on / 依赖: measurable_pi_apply
-/
theorem Measurable.eval {a : δ} {g : α -> forall a, X a} (hg : Measurable g) :
    Measurable fun x => g x a :=
  (measurable_pi_apply a).comp hg

@[fun_prop]
/--
theorem `measurable_pi_lambda` / 定理 `measurable_pi_lambda`

English:
theorem measurable_pi_lambda
  given: (f : α -> forall a, X a) (hf : forall a, Measurable fun c => f c a)
  proof: measurable_pi_iff.mpr hf

中文:
定理 measurable_pi_lambda
  条件: (f : α -> 对任意 a, X a) (hf : 对任意 a, Measurable fun c => f c a)
  证明: measurable_pi_iff.mpr hf

Depends on / 依赖: measurable_pi_iff, measurable_pi_iff.mpr
-/
theorem measurable_pi_lambda (f : α -> forall a, X a) (hf : forall a, Measurable fun c => f c a) :
    Measurable f :=
  measurable_pi_iff.mpr hf

/--
lemma `MeasurableSpace.comap_process_pi` / 引理 `MeasurableSpace.comap_process_pi`

English:
lemma MeasurableSpace.comap_process_pi
  given: (X : (a : δ) -> β -> X a)
  proof: by
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

中文:
引理 MeasurableSpace.comap_process_pi
  条件: (X : (a : δ) -> β -> X a)
  证明: by
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

Depends on / 依赖: MeasurableSpace, MeasurableSpace.comap_comp, MeasurableSpace.comap_iSup, MeasurableSpace.pi, comap_comp, comap_iSup, simp_rw
-/
lemma MeasurableSpace.comap_process_pi (X : (a : δ) -> β -> X a) :
    MeasurableSpace.comap (fun b a => X a b) inferInstance =
      ⨆ a, MeasurableSpace.comap (X a) inferInstance := by
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

/-- The function `(f, x) ↦ update f a x : (Π a, X a) × X a → Π a, X a` is measurable. -/
@[fun_prop]
/--
theorem `measurable_update'` / 定理 `measurable_update'`

English:
theorem measurable_update'
  given: {a : δ} [DecidableEq δ]
  proof: by
  rw [measurable_pi_iff]
  intro j
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_pi_iff.1 measurable_fst _

@[fun_prop]

中文:
定理 measurable_update'
  条件: {a : δ} [DecidableEq δ]
  证明: by
  rw [measurable_pi_iff]
  intro j
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_pi_iff.1 measurable_fst _

@[fun_prop]

Depends on / 依赖: measurable_fst, measurable_pi_iff, measurable_snd, split_ifs, update
-/
theorem measurable_update' {a : δ} [DecidableEq δ] :
    Measurable (fun p : (forall i, X i) × X a => update p.1 a p.2) := by
  rw [measurable_pi_iff]
  intro j
  dsimp [update]
  split_ifs with h
  · subst h
    dsimp
    exact measurable_snd
  · exact measurable_pi_iff.1 measurable_fst _

@[fun_prop]
/--
theorem `measurable_uniqueElim` / 定理 `measurable_uniqueElim`

English:
theorem measurable_uniqueElim
  given: [Unique δ]
  proof: by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

@[fun_prop]

中文:
定理 measurable_uniqueElim
  条件: [Unique δ]
  证明: by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

@[fun_prop]

Depends on / 依赖: Unique, Unique.forall_iff, forall_iff, measurable_id, measurable_pi_iff, simp_rw, uniqueElim_default
-/
theorem measurable_uniqueElim [Unique δ] :
    Measurable (uniqueElim : X (default : δ) -> forall i, X i) := by
  simp_rw [measurable_pi_iff, Unique.forall_iff, uniqueElim_default]; exact measurable_id

@[fun_prop]
/--
theorem `measurable_updateFinset'` / 定理 `measurable_updateFinset'`

English:
theorem measurable_updateFinset'
  given: [DecidableEq δ] {s : Finset δ}
  proof: by
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i in s <;> simp [h, Measurable.eval, measurable_fst, measurable_snd]

@[fun_prop]

中文:
定理 measurable_updateFinset'
  条件: [DecidableEq δ] {s : Finset δ}
  证明: by
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i in s <;> simp [h, Measurable.eval, measurable_fst, measurable_snd]

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.eval, measurable_fst, measurable_pi_iff, measurable_snd, updateFinset
-/
theorem measurable_updateFinset' [DecidableEq δ] {s : Finset δ} :
    Measurable (fun p : (Π i, X i) × (Π i : s, X i) => updateFinset p.1 s p.2) := by
  simp only [updateFinset, measurable_pi_iff]
  intro i
  by_cases h : i in s <;> simp [h, Measurable.eval, measurable_fst, measurable_snd]

@[fun_prop]
/--
theorem `measurable_updateFinset` / 定理 `measurable_updateFinset`

English:
theorem measurable_updateFinset
  given: [DecidableEq δ] {s : Finset δ} {x : Π i, X i}
  proof: measurable_updateFinset'.comp measurable_prodMk_left

@[fun_prop]

中文:
定理 measurable_updateFinset
  条件: [DecidableEq δ] {s : Finset δ} {x : Π i, X i}
  证明: measurable_updateFinset'.comp measurable_prodMk_left

@[fun_prop]

Depends on / 依赖: measurable_prodMk_left, measurable_updateFinset
-/
theorem measurable_updateFinset [DecidableEq δ] {s : Finset δ} {x : Π i, X i} :
    Measurable (updateFinset x s) :=
  measurable_updateFinset'.comp measurable_prodMk_left

@[fun_prop]
/--
theorem `measurable_updateFinset_left` / 定理 `measurable_updateFinset_left`

English:
theorem measurable_updateFinset_left
  given: [DecidableEq δ] {s : Finset δ} {x : Π i : s, X i}
  proof: measurable_updateFinset'.comp measurable_prodMk_right

中文:
定理 measurable_updateFinset_left
  条件: [DecidableEq δ] {s : Finset δ} {x : Π i : s, X i}
  证明: measurable_updateFinset'.comp measurable_prodMk_right

Depends on / 依赖: measurable_prodMk_right, measurable_updateFinset
-/
theorem measurable_updateFinset_left [DecidableEq δ] {s : Finset δ} {x : Π i : s, X i} :
    Measurable (updateFinset · s x) :=
  measurable_updateFinset'.comp measurable_prodMk_right

/-- The function `update f a : X a → Π a, X a` is always measurable.
  This doesn't require `f` to be measurable.
  This should not be confused with the statement that `update f a x` is measurable. -/
@[fun_prop]
/--
theorem `measurable_update` / 定理 `measurable_update`

English:
theorem measurable_update
  given: (f : forall a : δ, X a) {a : δ} [DecidableEq δ]
  statement: Measurable (update f a)
  proof: measurable_update'.comp measurable_prodMk_left

@[fun_prop]

中文:
定理 measurable_update
  条件: (f : 对任意 a : δ, X a) {a : δ} [DecidableEq δ]
  结论: Measurable (update f a)
  证明: measurable_update'.comp measurable_prodMk_left

@[fun_prop]

Depends on / 依赖: measurable_prodMk_left, measurable_update
-/
theorem measurable_update (f : forall a : δ, X a) {a : δ} [DecidableEq δ] : Measurable (update f a) :=
  measurable_update'.comp measurable_prodMk_left

@[fun_prop]
/--
theorem `measurable_update_left` / 定理 `measurable_update_left`

English:
theorem measurable_update_left
  given: {a : δ} [DecidableEq δ] {x : X a}
  proof: measurable_update'.comp measurable_prodMk_right

@[fun_prop]

中文:
定理 measurable_update_left
  条件: {a : δ} [DecidableEq δ] {x : X a}
  证明: measurable_update'.comp measurable_prodMk_right

@[fun_prop]

Depends on / 依赖: measurable_prodMk_right, measurable_update
-/
theorem measurable_update_left {a : δ} [DecidableEq δ] {x : X a} :
    Measurable (update · a x) :=
  measurable_update'.comp measurable_prodMk_right

@[fun_prop]
/--
theorem `Set.measurable_restrict` / 定理 `Set.measurable_restrict`

English:
theorem Set.measurable_restrict
  given: (s : Set δ)
  statement: Measurable (s.domRestrict (π := X))
  proof: measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]

中文:
定理 Set.measurable_restrict
  条件: (s : Set δ)
  结论: Measurable (s.domRestrict (π := X))
  证明: measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]
-/
theorem Set.measurable_restrict (s : Set δ) : Measurable (s.domRestrict (π := X)) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]
/--
theorem `Set.measurable_restrict₂` / 定理 `Set.measurable_restrict₂`

English:
theorem Set.measurable_restrict₂
  given: {s t : Set δ} (hst : s subseteq t)
  proof: measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]

中文:
定理 Set.measurable_restrict₂
  条件: {s t : Set δ} (hst : s subseteq t)
  证明: measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]
-/
theorem Set.measurable_restrict₂ {s t : Set δ} (hst : s subseteq t) :
    Measurable (domRestrict₂ (π := X) hst) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]
/--
theorem `Finset.measurable_restrict` / 定理 `Finset.measurable_restrict`

English:
theorem Finset.measurable_restrict
  given: (s : Finset δ)
  statement: Measurable (s.restrict (π := X))
  proof: measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]

中文:
定理 Finset.measurable_restrict
  条件: (s : Finset δ)
  结论: Measurable (s.restrict (π := X))
  证明: measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]
-/
theorem Finset.measurable_restrict (s : Finset δ) : Measurable (s.restrict (π := X)) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]
/--
theorem `Finset.measurable_restrict₂` / 定理 `Finset.measurable_restrict₂`

English:
theorem Finset.measurable_restrict₂
  given: {s t : Finset δ} (hst : s subseteq t)
  proof: measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]

中文:
定理 Finset.measurable_restrict₂
  条件: {s t : Finset δ} (hst : s subseteq t)
  证明: measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]
-/
theorem Finset.measurable_restrict₂ {s t : Finset δ} (hst : s subseteq t) :
    Measurable (Finset.restrict₂ (π := X) hst) :=
  measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]
/--
theorem `Set.measurable_restrict_apply` / 定理 `Set.measurable_restrict_apply`

English:
theorem Set.measurable_restrict_apply
  given: (s : Set α) {f : α -> γ} (hf : Measurable f)
  proof: hf.comp measurable_subtype_coe

@[fun_prop]

中文:
定理 Set.measurable_restrict_apply
  条件: (s : Set α) {f : α -> γ} (hf : Measurable f)
  证明: hf.comp measurable_subtype_coe

@[fun_prop]

Depends on / 依赖: hf.comp, measurable_subtype_coe
-/
theorem Set.measurable_restrict_apply (s : Set α) {f : α -> γ} (hf : Measurable f) :
    Measurable (s.domRestrict f) := hf.comp measurable_subtype_coe

@[fun_prop]
/--
theorem `Set.measurable_restrict₂_apply` / 定理 `Set.measurable_restrict₂_apply`

English:
theorem Set.measurable_restrict₂_apply
  statement: {s t : Set α} (hst : s subseteq t)
  proof: hf.comp (measurable_inclusion hst)

@[fun_prop]

中文:
定理 Set.measurable_restrict₂_apply
  结论: {s t : Set α} (hst : s subseteq t)
  证明: hf.comp (measurable_inclusion hst)

@[fun_prop]

Depends on / 依赖: hf.comp, measurable_inclusion
-/
theorem Set.measurable_restrict₂_apply {s t : Set α} (hst : s subseteq t)
    {f : t -> γ} (hf : Measurable f) :
    Measurable (domRestrict₂ (π := fun _ => γ) hst f) := hf.comp (measurable_inclusion hst)

@[fun_prop]
/--
theorem `Finset.measurable_restrict_apply` / 定理 `Finset.measurable_restrict_apply`

English:
theorem Finset.measurable_restrict_apply
  given: (s : Finset α) {f : α -> γ} (hf : Measurable f)
  proof: hf.comp measurable_subtype_coe

@[fun_prop]

中文:
定理 Finset.measurable_restrict_apply
  条件: (s : Finset α) {f : α -> γ} (hf : Measurable f)
  证明: hf.comp measurable_subtype_coe

@[fun_prop]

Depends on / 依赖: hf.comp, measurable_subtype_coe
-/
theorem Finset.measurable_restrict_apply (s : Finset α) {f : α -> γ} (hf : Measurable f) :
    Measurable (s.restrict f) := hf.comp measurable_subtype_coe

@[fun_prop]
/--
theorem `Finset.measurable_restrict₂_apply` / 定理 `Finset.measurable_restrict₂_apply`

English:
theorem Finset.measurable_restrict₂_apply
  statement: {s t : Finset α} (hst : s subseteq t)
  proof: hf.comp (measurable_inclusion hst)

中文:
定理 Finset.measurable_restrict₂_apply
  结论: {s t : Finset α} (hst : s subseteq t)
  证明: hf.comp (measurable_inclusion hst)

Depends on / 依赖: hf.comp, measurable_inclusion
-/
theorem Finset.measurable_restrict₂_apply {s t : Finset α} (hst : s subseteq t)
    {f : t -> γ} (hf : Measurable f) :
    Measurable (restrict₂ (π := fun _ => γ) hst f) := hf.comp (measurable_inclusion hst)

variable (X) in
/--
theorem `measurable_eq_mp` / 定理 `measurable_eq_mp`

English:
theorem measurable_eq_mp
  given: {i i' : δ} (h : i = i')
  statement: Measurable (congr_arg X h).mp
  proof: by
  cases h
  exact measurable_id

中文:
定理 measurable_eq_mp
  条件: {i i' : δ} (h : i = i')
  结论: Measurable (congr_arg X h).mp
  证明: by
  cases h
  exact measurable_id

Depends on / 依赖: measurable_id
-/
theorem measurable_eq_mp {i i' : δ} (h : i = i') : Measurable (congr_arg X h).mp := by
  cases h
  exact measurable_id

variable (X) in
/--
theorem `Measurable.eq_mp` / 定理 `Measurable.eq_mp`

English:
theorem Measurable.eq_mp
  statement: {β} [MeasurableSpace β] {i i' : δ} (h : i = i') {f : β -> X i}
  proof: (measurable_eq_mp X h).comp hf

@[fun_prop]

中文:
定理 Measurable.eq_mp
  结论: {β} [MeasurableSpace β] {i i' : δ} (h : i = i') {f : β -> X i}
  证明: (measurable_eq_mp X h).comp hf

@[fun_prop]

Depends on / 依赖: measurable_eq_mp
-/
theorem Measurable.eq_mp {β} [MeasurableSpace β] {i i' : δ} (h : i = i') {f : β -> X i}
    (hf : Measurable f) : Measurable fun x => (congr_arg X h).mp (f x) :=
  (measurable_eq_mp X h).comp hf

@[fun_prop]
/--
theorem `measurable_piCongrLeft` / 定理 `measurable_piCongrLeft`

English:
theorem measurable_piCongrLeft
  given: (f : δ' ≃ δ)
  statement: Measurable (Equiv.piCongrLeft X f)
  proof: by
  rw [measurable_pi_iff]
  intro i
  simp_rw [Equiv.piCongrLeft_apply_eq_cast]
exact Measurable.eq_mp X (f.apply_symm_apply i) measurable_pi_apply f.symm i

中文:
定理 measurable_piCongrLeft
  条件: (f : δ' ≃ δ)
  结论: Measurable (Equiv.piCongrLeft X f)
  证明: by
  rw [measurable_pi_iff]
  intro i
  simp_rw [Equiv.piCongrLeft_apply_eq_cast]
exact Measurable.eq_mp X (f.apply_symm_apply i) measurable_pi_apply f.symm i

Depends on / 依赖: Equiv.piCongrLeft_apply_eq_cast, Measurable, Measurable.eq_mp, apply_symm_apply, eq_mp, f.apply_symm_apply, f.symm, measurable_pi_apply, measurable_pi_iff, piCongrLeft_apply_eq_cast, simp_rw
-/
theorem measurable_piCongrLeft (f : δ' ≃ δ) : Measurable (Equiv.piCongrLeft X f) := by
  rw [measurable_pi_iff]
  intro i
  simp_rw [Equiv.piCongrLeft_apply_eq_cast]
exact Measurable.eq_mp X (f.apply_symm_apply i) measurable_pi_apply f.symm i

/- Even though we cannot use projection notation, we still keep a dot to be consistent with similar
lemmas, like `MeasurableSet.prod`. -/
@[measurability]
/--
theorem `MeasurableSet.pi` / 定理 `MeasurableSet.pi`

English:
theorem MeasurableSet.pi
  statement: {s : Set δ} {t : forall i : δ, Set (X i)} (hs : s.Countable)
  proof: by
  rw [pi_def]
  exact MeasurableSet.biInter hs fun i hi => measurable_pi_apply _ (ht i hi)

中文:
定理 MeasurableSet.pi
  结论: {s : Set δ} {t : 对任意 i : δ, Set (X i)} (hs : s.Countable)
  证明: by
  rw [pi_def]
  exact MeasurableSet.biInter hs fun i hi => measurable_pi_apply _ (ht i hi)
-/
protected theorem MeasurableSet.pi {s : Set δ} {t : forall i : δ, Set (X i)} (hs : s.Countable)
    (ht : forall i in s, MeasurableSet (t i)) : MeasurableSet (s.pi t) := by
  rw [pi_def]
  exact MeasurableSet.biInter hs fun i hi => measurable_pi_apply _ (ht i hi)

/--
theorem `MeasurableSet.univ_pi` / 定理 `MeasurableSet.univ_pi`

English:
theorem MeasurableSet.univ_pi
  statement: [Countable δ] {t : forall i : δ, Set (X i)}
  proof: MeasurableSet.pi (to_countable _) fun i _ => ht i

中文:
定理 MeasurableSet.univ_pi
  结论: [Countable δ] {t : 对任意 i : δ, Set (X i)}
  证明: MeasurableSet.pi (to_countable _) fun i _ => ht i
-/
protected theorem MeasurableSet.univ_pi [Countable δ] {t : forall i : δ, Set (X i)}
    (ht : forall i, MeasurableSet (t i)) : MeasurableSet (pi univ t) :=
  MeasurableSet.pi (to_countable _) fun i _ => ht i

/--
theorem `MeasurableSet.univ_pi'` / 定理 `MeasurableSet.univ_pi'`

English:
theorem MeasurableSet.univ_pi'
  statement: [Countable δ] {t : forall i : δ, Set (X i)}
  proof: (MeasurableSet.univ_pi ht).congr (by grind)

中文:
定理 MeasurableSet.univ_pi'
  结论: [Countable δ] {t : 对任意 i : δ, Set (X i)}
  证明: (MeasurableSet.univ_pi ht).congr (by grind)

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, univ_pi
-/
theorem MeasurableSet.univ_pi' [Countable δ] {t : forall i : δ, Set (X i)}
    (ht : forall i, MeasurableSet (t i)) : MeasurableSet {f : forall i : δ, X i | forall i : δ, f i in t i} :=
  (MeasurableSet.univ_pi ht).congr (by grind)

/--
theorem `measurableSet_pi_of_nonempty` / 定理 `measurableSet_pi_of_nonempty`

English:
theorem measurableSet_pi_of_nonempty
  statement: {s : Set δ} {t : forall i, Set (X i)} (hs : s.Countable)
  proof: by
  classical
    rcases h with ⟨f, hf⟩
    refine ⟨fun hst i hi => ?_, MeasurableSet.pi hs⟩
    convert! measurable_update f (a := i) hst
    rw [update_preimage_pi hi]
    exact fun j hj _ => hf j hj

中文:
定理 measurableSet_pi_of_nonempty
  结论: {s : Set δ} {t : 对任意 i, Set (X i)} (hs : s.Countable)
  证明: by
  classical
    rcases h with ⟨f, hf⟩
    refine ⟨fun hst i hi => ?_, MeasurableSet.pi hs⟩
    convert! measurable_update f (a := i) hst
    rw [update_preimage_pi hi]
    exact fun j hj _ => hf j hj

Depends on / 依赖: MeasurableSet, MeasurableSet.pi, classical, convert, measurable_update, update_preimage_pi
-/
theorem measurableSet_pi_of_nonempty {s : Set δ} {t : forall i, Set (X i)} (hs : s.Countable)
    (h : (pi s t).Nonempty) : MeasurableSet (pi s t) ↔ forall i in s, MeasurableSet (t i) := by
  classical
    rcases h with ⟨f, hf⟩
    refine ⟨fun hst i hi => ?_, MeasurableSet.pi hs⟩
    convert! measurable_update f (a := i) hst
    rw [update_preimage_pi hi]
    exact fun j hj _ => hf j hj

/--
theorem `measurableSet_pi` / 定理 `measurableSet_pi`

English:
theorem measurableSet_pi
  given: {s : Set δ} {t : forall i, Set (X i)} (hs : s.Countable)
  proof: by
  rcases (pi s t).eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [measurableSet_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty]

中文:
定理 measurableSet_pi
  条件: {s : Set δ} {t : 对任意 i, Set (X i)} (hs : s.Countable)
  证明: by
  rcases (pi s t).eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [measurableSet_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty]

Depends on / 依赖: eq_empty_or_nonempty, measurableSet_pi_of_nonempty, not_nonempty_iff_eq_empty
-/
theorem measurableSet_pi {s : Set δ} {t : forall i, Set (X i)} (hs : s.Countable) :
    MeasurableSet (pi s t) ↔ (forall i in s, MeasurableSet (t i)) ∨ pi s t = ∅ := by
  rcases (pi s t).eq_empty_or_nonempty with h | h
  · simp [h]
  · simp [measurableSet_pi_of_nonempty hs, h, ← not_nonempty_iff_eq_empty]

/--
Instance `Pi.instMeasurableSingletonClass` / 实例 `Pi.instMeasurableSingletonClass`

English:
instance Pi.instMeasurableSingletonClass
  signature: [Countable δ] [forall a, MeasurableSingletonClass (X a)]
  body: ⟨fun f => univ_pi_singleton f ▸ MeasurableSet.univ_pi fun t => measurableSet_singleton (f t)⟩

中文:
实例 Pi.instMeasurableSingletonClass
  签名: [Countable δ] [对任意 a, MeasurableSingletonClass (X a)]
  定义体: ⟨fun f => univ_pi_singleton f ▸ MeasurableSet.univ_pi fun t => measurableSet_singleton (f t)⟩

Depends on / 依赖: MeasurableSet, MeasurableSet.univ_pi, measurableSet_singleton, univ_pi, univ_pi_singleton
-/
instance Pi.instMeasurableSingletonClass [Countable δ] [forall a, MeasurableSingletonClass (X a)] :
    MeasurableSingletonClass (forall a, X a) :=
  ⟨fun f => univ_pi_singleton f ▸ MeasurableSet.univ_pi fun t => measurableSet_singleton (f t)⟩

variable (X)

@[fun_prop]
/--
theorem `measurable_piEquivPiSubtypeProd_symm` / 定理 `measurable_piEquivPiSubtypeProd_symm`

English:
theorem measurable_piEquivPiSubtypeProd_symm
  given: (p : δ -> Prop) [DecidablePred p]
  proof: by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : p j
  · simp only [hj, dif_pos, Equiv.piEquivPiSubtypeProd_symm_apply]
    have : Measurable fun (f : forall i : { x // p x }, X i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (X := fun i : {x // p x} => X i.1) ⟨j, hj⟩
    exact Measurable.

中文:
定理 measurable_piEquivPiSubtypeProd_symm
  条件: (p : δ -> 命题) [DecidablePred p]
  证明: by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : p j
  · simp only [hj, dif_pos, Equiv.piEquivPiSubtypeProd_symm_apply]
    have : Measurable fun (f : forall i : { x // p x }, X i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (X := fun i : {x // p x} => X i.1) ⟨j, hj⟩
    exact Measurable.

Depends on / 依赖: Equiv.piEquivPiSubtypeProd_symm_apply, Measurable, Measurable.comp, dif_neg, dif_pos, measurable_fst, measurable_pi_apply, measurable_pi_iff, not_false_iff, piEquivPiSubtypeProd_symm_apply
-/
theorem measurable_piEquivPiSubtypeProd_symm (p : δ -> Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p X).symm := by
  refine measurable_pi_iff.2 fun j => ?_
  by_cases hj : p j
  · simp only [hj, dif_pos, Equiv.piEquivPiSubtypeProd_symm_apply]
    have : Measurable fun (f : forall i : { x // p x }, X i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (X := fun i : {x // p x} => X i.1) ⟨j, hj⟩
    exact Measurable.comp this measurable_fst
  · simp only [hj, Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg, not_false_iff]
    have : Measurable fun (f : forall i : { x // ¬p x }, X i.1) => f ⟨j, hj⟩ :=
      measurable_pi_apply (X := fun i : {x // ¬p x} => X i.1) ⟨j, hj⟩
    exact Measurable.comp this measurable_snd

@[fun_prop]
/--
theorem `measurable_piEquivPiSubtypeProd` / 定理 `measurable_piEquivPiSubtypeProd`

English:
theorem measurable_piEquivPiSubtypeProd
  given: (p : δ -> Prop) [DecidablePred p]
  proof: (measurable_pi_iff.2 fun _ => measurable_pi_apply _).prodMk
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

中文:
定理 measurable_piEquivPiSubtypeProd
  条件: (p : δ -> 命题) [DecidablePred p]
  证明: (measurable_pi_iff.2 fun _ => measurable_pi_apply _).prodMk
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

Depends on / 依赖: measurable_pi_apply, measurable_pi_iff, prodMk
-/
theorem measurable_piEquivPiSubtypeProd (p : δ -> Prop) [DecidablePred p] :
    Measurable (Equiv.piEquivPiSubtypeProd p X) :=
  (measurable_pi_iff.2 fun _ => measurable_pi_apply _).prodMk
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)

end Pi

/--
Instance `TProd.instMeasurableSpace` / 实例 `TProd.instMeasurableSpace`

English:
instance TProd.instMeasurableSpace
  signature: (X : δ -> Type*) [forall i, MeasurableSpace (X i)]

中文:
实例 TProd.instMeasurableSpace
  签名: (X : δ -> 类型) [对任意 i, MeasurableSpace (X i)]
-/
instance TProd.instMeasurableSpace (X : δ -> Type*) [forall i, MeasurableSpace (X i)] :
    forall l : List δ, MeasurableSpace (List.TProd X l)
  | [] => PUnit.instMeasurableSpace
  | _::is => @Prod.instMeasurableSpace _ _ _ (TProd.instMeasurableSpace X is)

section TProd

open List

variable {X : δ -> Type*} [forall i, MeasurableSpace (X i)]

/--
theorem `measurable_tProd_mk` / 定理 `measurable_tProd_mk`

English:
theorem measurable_tProd_mk
  given: (l : List δ)
  statement: Measurable (@TProd.mk δ X l)
  proof: by
  induction l with
  | nil => exact measurable_const
  | cons i l ih => exact (measurable_pi_apply i).prodMk ih

中文:
定理 measurable_tProd_mk
  条件: (l : List δ)
  结论: Measurable (@TProd.mk δ X l)
  证明: by
  induction l with
  | nil => exact measurable_const
  | cons i l ih => exact (measurable_pi_apply i).prodMk ih

Depends on / 依赖: measurable_const, measurable_pi_apply, prodMk
-/
theorem measurable_tProd_mk (l : List δ) : Measurable (@TProd.mk δ X l) := by
  induction l with
  | nil => exact measurable_const
  | cons i l ih => exact (measurable_pi_apply i).prodMk ih

set_option backward.isDefEq.respectTransparency false in
/--
theorem `measurable_tProd_elim` / 定理 `measurable_tProd_elim`

English:
theorem measurable_tProd_elim
  given: [DecidableEq δ]

中文:
定理 measurable_tProd_elim
  条件: [DecidableEq δ]
-/
theorem measurable_tProd_elim [DecidableEq δ] :
    forall {l : List δ} {i : δ} (hi : i in l), Measurable fun v : TProd X l => v.elim hi
  | i::is, j, hj => by
    by_cases hji : j = i
    · subst hji
      simpa using measurable_fst
    · simp only [TProd.elim_of_ne _ hji]
      rw [mem_cons] at hj
      exact (measurable_tProd_elim (hj.resolve_left hji)).comp measurable_snd

/--
theorem `measurable_tProd_elim'` / 定理 `measurable_tProd_elim'`

English:
theorem measurable_tProd_elim'
  given: [DecidableEq δ] {l : List δ} (h : forall i, i in l)
  proof: measurable_pi_lambda _ fun i => measurable_tProd_elim (h i)

中文:
定理 measurable_tProd_elim'
  条件: [DecidableEq δ] {l : List δ} (h : 对任意 i, i in l)
  证明: measurable_pi_lambda _ fun i => measurable_tProd_elim (h i)

Depends on / 依赖: measurable_pi_lambda, measurable_tProd_elim
-/
theorem measurable_tProd_elim' [DecidableEq δ] {l : List δ} (h : forall i, i in l) :
    Measurable (TProd.elim' h : TProd X l -> forall i, X i) :=
  measurable_pi_lambda _ fun i => measurable_tProd_elim (h i)

/--
theorem `MeasurableSet.tProd` / 定理 `MeasurableSet.tProd`

English:
theorem MeasurableSet.tProd
  given: (l : List δ) {s : forall i, Set (X i)} (hs : forall i, MeasurableSet (s i))
  proof: by
  induction l with
  | nil => exact MeasurableSet.univ
  | cons i l ih => exact (hs i).prod ih

中文:
定理 MeasurableSet.tProd
  条件: (l : List δ) {s : 对任意 i, Set (X i)} (hs : 对任意 i, MeasurableSet (s i))
  证明: by
  induction l with
  | nil => exact MeasurableSet.univ
  | cons i l ih => exact (hs i).prod ih

Depends on / 依赖: MeasurableSet, MeasurableSet.univ
-/
theorem MeasurableSet.tProd (l : List δ) {s : forall i, Set (X i)} (hs : forall i, MeasurableSet (s i)) :
    MeasurableSet (Set.tprod l s) := by
  induction l with
  | nil => exact MeasurableSet.univ
  | cons i l ih => exact (hs i).prod ih

end TProd

/--
Instance `Sum.instMeasurableSpace` / 实例 `Sum.instMeasurableSpace`

English:
instance Sum.instMeasurableSpace
  signature: {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β]
  body: m₁.map Sum.inl ⊓ m₂.map Sum.inr

中文:
实例 Sum.instMeasurableSpace
  签名: {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β]
  定义体: m₁.map Sum.inl ⊓ m₂.map Sum.inr

Depends on / 依赖: Sum.inl, Sum.inr
-/
instance Sum.instMeasurableSpace {α β} [m₁ : MeasurableSpace α] [m₂ : MeasurableSpace β] :
    MeasurableSpace (α oplus β) :=
  m₁.map Sum.inl ⊓ m₂.map Sum.inr

section Sum

@[fun_prop]
/--
theorem `measurable_inl` / 定理 `measurable_inl`

English:
theorem measurable_inl
  given: [MeasurableSpace α] [MeasurableSpace β]
  statement: Measurable (@Sum.inl α β)
  proof: Measurable.of_le_map inf_le_left

@[fun_prop]

中文:
定理 measurable_inl
  条件: [MeasurableSpace α] [MeasurableSpace β]
  结论: Measurable (@Sum.inl α β)
  证明: Measurable.of_le_map inf_le_left

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.of_le_map, inf_le_left, of_le_map
-/
theorem measurable_inl [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.inl α β) :=
  Measurable.of_le_map inf_le_left

@[fun_prop]
/--
theorem `measurable_inr` / 定理 `measurable_inr`

English:
theorem measurable_inr
  given: [MeasurableSpace α] [MeasurableSpace β]
  statement: Measurable (@Sum.inr α β)
  proof: Measurable.of_le_map inf_le_right

中文:
定理 measurable_inr
  条件: [MeasurableSpace α] [MeasurableSpace β]
  结论: Measurable (@Sum.inr α β)
  证明: Measurable.of_le_map inf_le_right

Depends on / 依赖: Measurable, Measurable.of_le_map, inf_le_right, of_le_map
-/
theorem measurable_inr [MeasurableSpace α] [MeasurableSpace β] : Measurable (@Sum.inr α β) :=
  Measurable.of_le_map inf_le_right

variable {m : MeasurableSpace α} {mβ : MeasurableSpace β}

/--
theorem `measurableSet_sum_iff` / 定理 `measurableSet_sum_iff`

English:
theorem measurableSet_sum_iff
  given: {s : Set (α oplus β)}
  proof: Iff.rfl

中文:
定理 measurableSet_sum_iff
  条件: {s : Set (α oplus β)}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem measurableSet_sum_iff {s : Set (α oplus β)} :
    MeasurableSet s ↔ MeasurableSet (Sum.inl ⁻¹' s) ∧ MeasurableSet (Sum.inr ⁻¹' s) :=
  Iff.rfl

/--
theorem `measurable_fun_sum` / 定理 `measurable_fun_sum`

English:
theorem measurable_fun_sum
  statement: {_ : MeasurableSpace γ} {f : α oplus β -> γ} (hl : Measurable (f ∘ Sum.inl))
  proof: Measurable.of_comap_le
    le_inf (MeasurableSpace.comap_le_iff_le_map.2 <| hl)
      (MeasurableSpace.comap_le_iff_le_map.2 <| hr)

@[fun_prop]

中文:
定理 measurable_fun_sum
  结论: {_ : MeasurableSpace γ} {f : α oplus β -> γ} (hl : Measurable (f ∘ Sum.inl))
  证明: Measurable.of_comap_le
    le_inf (MeasurableSpace.comap_le_iff_le_map.2 <| hl)
      (MeasurableSpace.comap_le_iff_le_map.2 <| hr)

@[fun_prop]

Depends on / 依赖: Measurable, Measurable.of_comap_le, MeasurableSpace, MeasurableSpace.comap_le_iff_le_map, comap_le_iff_le_map, le_inf, of_comap_le
-/
theorem measurable_fun_sum {_ : MeasurableSpace γ} {f : α oplus β -> γ} (hl : Measurable (f ∘ Sum.inl))
    (hr : Measurable (f ∘ Sum.inr)) : Measurable f :=
Measurable.of_comap_le
    le_inf (MeasurableSpace.comap_le_iff_le_map.2 <| hl)
      (MeasurableSpace.comap_le_iff_le_map.2 <| hr)

@[fun_prop]
/--
theorem `Measurable.sumElim` / 定理 `Measurable.sumElim`

English:
theorem Measurable.sumElim
  statement: {_ : MeasurableSpace γ} {f : α -> γ} {g : β -> γ} (hf : Measurable f)
  proof: measurable_fun_sum hf hg

中文:
定理 Measurable.sumElim
  结论: {_ : MeasurableSpace γ} {f : α -> γ} {g : β -> γ} (hf : Measurable f)
  证明: measurable_fun_sum hf hg

Depends on / 依赖: measurable_fun_sum
-/
theorem Measurable.sumElim {_ : MeasurableSpace γ} {f : α -> γ} {g : β -> γ} (hf : Measurable f)
    (hg : Measurable g) : Measurable (Sum.elim f g) :=
  measurable_fun_sum hf hg

/--
theorem `Measurable.sumMap` / 定理 `Measurable.sumMap`

English:
theorem Measurable.sumMap
  statement: {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {f : α -> β} {g : γ -> δ}
  proof: (measurable_inl.comp hf).sumElim (measurable_inr.comp hg)

中文:
定理 Measurable.sumMap
  结论: {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {f : α -> β} {g : γ -> δ}
  证明: (measurable_inl.comp hf).sumElim (measurable_inr.comp hg)

Depends on / 依赖: measurable_inl, measurable_inl.comp, measurable_inr, measurable_inr.comp, sumElim
-/
theorem Measurable.sumMap {_ : MeasurableSpace γ} {_ : MeasurableSpace δ} {f : α -> β} {g : γ -> δ}
    (hf : Measurable f) (hg : Measurable g) : Measurable (Sum.map f g) :=
  (measurable_inl.comp hf).sumElim (measurable_inr.comp hg)

/--
theorem `measurableSet_inl_image` / 定理 `measurableSet_inl_image`

English:
theorem measurableSet_inl_image
  given: {s : Set α}
  proof: by
  simp [measurableSet_sum_iff, Sum.inl_injective.preimage_image]

alias ⟨_, MeasurableSet.inl_image⟩ := measurableSet_inl_image

中文:
定理 measurableSet_inl_image
  条件: {s : Set α}
  证明: by
  simp [measurableSet_sum_iff, Sum.inl_injective.preimage_image]

alias ⟨_, MeasurableSet.inl_image⟩ := measurableSet_inl_image
-/
@[simp] theorem measurableSet_inl_image {s : Set α} :
    MeasurableSet (Sum.inl '' s : Set (α oplus β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inl_injective.preimage_image]

alias ⟨_, MeasurableSet.inl_image⟩ := measurableSet_inl_image

/--
theorem `measurableSet_inr_image` / 定理 `measurableSet_inr_image`

English:
theorem measurableSet_inr_image
  given: {s : Set β}
  proof: by
  simp [measurableSet_sum_iff, Sum.inr_injective.preimage_image]

alias ⟨_, MeasurableSet.inr_image⟩ := measurableSet_inr_image

中文:
定理 measurableSet_inr_image
  条件: {s : Set β}
  证明: by
  simp [measurableSet_sum_iff, Sum.inr_injective.preimage_image]

alias ⟨_, MeasurableSet.inr_image⟩ := measurableSet_inr_image
-/
@[simp] theorem measurableSet_inr_image {s : Set β} :
    MeasurableSet (Sum.inr '' s : Set (α oplus β)) ↔ MeasurableSet s := by
  simp [measurableSet_sum_iff, Sum.inr_injective.preimage_image]

alias ⟨_, MeasurableSet.inr_image⟩ := measurableSet_inr_image

/--
theorem `measurableSet_range_inl` / 定理 `measurableSet_range_inl`

English:
theorem measurableSet_range_inl
  given: [MeasurableSpace α]
  proof: by
  rw [← image_univ]
  exact MeasurableSet.univ.inl_image

中文:
定理 measurableSet_range_inl
  条件: [MeasurableSpace α]
  证明: by
  rw [← image_univ]
  exact MeasurableSet.univ.inl_image

Depends on / 依赖: MeasurableSet, MeasurableSet.univ.inl_image, image_univ, inl_image
-/
theorem measurableSet_range_inl [MeasurableSpace α] :
    MeasurableSet (range Sum.inl : Set (α oplus β)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.inl_image

/--
theorem `measurableSet_range_inr` / 定理 `measurableSet_range_inr`

English:
theorem measurableSet_range_inr
  given: [MeasurableSpace α]
  proof: by
  rw [← image_univ]
  exact MeasurableSet.univ.inr_image

中文:
定理 measurableSet_range_inr
  条件: [MeasurableSpace α]
  证明: by
  rw [← image_univ]
  exact MeasurableSet.univ.inr_image

Depends on / 依赖: MeasurableSet, MeasurableSet.univ.inr_image, image_univ, inr_image
-/
theorem measurableSet_range_inr [MeasurableSpace α] :
    MeasurableSet (range Sum.inr : Set (α oplus β)) := by
  rw [← image_univ]
  exact MeasurableSet.univ.inr_image

end Sum

/--
Instance `Sigma.instMeasurableSpace` / 实例 `Sigma.instMeasurableSpace`

English:
instance Sigma.instMeasurableSpace
  signature: {α} {β : α -> Type*} [m : forall a, MeasurableSpace (β a)]
  body: ⨅ a, (m a).map (Sigma.mk a)

中文:
实例 Sigma.instMeasurableSpace
  签名: {α} {β : α -> 类型} [m : 对任意 a, MeasurableSpace (β a)]
  定义体: ⨅ a, (m a).map (Sigma.mk a)

Depends on / 依赖: Sigma.mk
-/
instance Sigma.instMeasurableSpace {α} {β : α -> Type*} [m : forall a, MeasurableSpace (β a)] :
    MeasurableSpace (Sigma β) :=
  ⨅ a, (m a).map (Sigma.mk a)

section prop
variable [MeasurableSpace α] {p q : α -> Prop}

/--
theorem `measurableSet_setOfPred` / 定理 `measurableSet_setOfPred`

English:
theorem measurableSet_setOfPred
  statement: MeasurableSet {a | p a} ↔ Measurable p
  proof: ⟨fun h => measurable_to_prop by simpa only [preimage_singleton_true], fun h => by
    simpa using h (measurableSet_singleton True)⟩

@[deprecated (since := "2026-07-09")] alias measurableSet_setOf := measurableSet_setOfPred

中文:
定理 measurableSet_setOfPred
  结论: MeasurableSet {a | p a} ↔ Measurable p
  证明: ⟨fun h => measurable_to_prop by simpa only [preimage_singleton_true], fun h => by
    simpa using h (measurableSet_singleton True)⟩

@[deprecated (since := "2026-07-09")] alias measurableSet_setOf := measurableSet_setOfPred
-/
@[simp] theorem measurableSet_setOfPred : MeasurableSet {a | p a} ↔ Measurable p :=
⟨fun h => measurable_to_prop by simpa only [preimage_singleton_true], fun h => by
    simpa using h (measurableSet_singleton True)⟩

@[deprecated (since := "2026-07-09")] alias measurableSet_setOf := measurableSet_setOfPred

/--
theorem `measurable_mem` / 定理 `measurable_mem`

English:
theorem measurable_mem
  statement: Measurable (· in s) ↔ MeasurableSet s
  proof: measurableSet_setOfPred.symm

alias ⟨_, Measurable.setOf⟩ := measurableSet_setOfPred

@[fun_prop]
alias ⟨_, MeasurableSet.mem⟩ := measurable_mem

@[fun_prop]

中文:
定理 measurable_mem
  结论: Measurable (· in s) ↔ MeasurableSet s
  证明: measurableSet_setOfPred.symm

alias ⟨_, Measurable.setOf⟩ := measurableSet_setOfPred

@[fun_prop]
alias ⟨_, MeasurableSet.mem⟩ := measurable_mem

@[fun_prop]
-/
@[simp] theorem measurable_mem : Measurable (· in s) ↔ MeasurableSet s :=
  measurableSet_setOfPred.symm

alias ⟨_, Measurable.setOf⟩ := measurableSet_setOfPred

@[fun_prop]
alias ⟨_, MeasurableSet.mem⟩ := measurable_mem

@[fun_prop]
/--
lemma `Measurable.not` / 引理 `Measurable.not`

English:
lemma Measurable.not
  given: (hp : Measurable p)
  statement: Measurable (¬ p ·)
  proof: measurableSet_setOfPred.1 hp.setOf.compl

@[fun_prop]

中文:
引理 Measurable.not
  条件: (hp : Measurable p)
  结论: Measurable (¬ p ·)
  证明: measurableSet_setOfPred.1 hp.setOf.compl

@[fun_prop]

Depends on / 依赖: hp.setOf.compl, measurableSet_setOfPred
-/
lemma Measurable.not (hp : Measurable p) : Measurable (¬ p ·) :=
  measurableSet_setOfPred.1 hp.setOf.compl

@[fun_prop]
/--
lemma `Measurable.and` / 引理 `Measurable.and`

English:
lemma Measurable.and
  given: (hp : Measurable p) (hq : Measurable q)
  statement: Measurable fun a => p a ∧ q a
  proof: measurableSet_setOfPred.1 hp.setOf.inter hq.setOf

@[fun_prop]

中文:
引理 Measurable.and
  条件: (hp : Measurable p) (hq : Measurable q)
  结论: Measurable fun a => p a ∧ q a
  证明: measurableSet_setOfPred.1 hp.setOf.inter hq.setOf

@[fun_prop]

Depends on / 依赖: hp.setOf.inter, hq.setOf, measurableSet_setOfPred
-/
lemma Measurable.and (hp : Measurable p) (hq : Measurable q) : Measurable fun a => p a ∧ q a :=
measurableSet_setOfPred.1 hp.setOf.inter hq.setOf

@[fun_prop]
/--
lemma `Measurable.or` / 引理 `Measurable.or`

English:
lemma Measurable.or
  given: (hp : Measurable p) (hq : Measurable q)
  statement: Measurable fun a => p a ∨ q a
  proof: measurableSet_setOfPred.1 hp.setOf.union hq.setOf

@[fun_prop]

中文:
引理 Measurable.or
  条件: (hp : Measurable p) (hq : Measurable q)
  结论: Measurable fun a => p a ∨ q a
  证明: measurableSet_setOfPred.1 hp.setOf.union hq.setOf

@[fun_prop]

Depends on / 依赖: hp.setOf.union, hq.setOf, measurableSet_setOfPred
-/
lemma Measurable.or (hp : Measurable p) (hq : Measurable q) : Measurable fun a => p a ∨ q a :=
measurableSet_setOfPred.1 hp.setOf.union hq.setOf

@[fun_prop]
/--
lemma `Measurable.imp` / 引理 `Measurable.imp`

English:
lemma Measurable.imp
  given: (hp : Measurable p) (hq : Measurable q)
  statement: Measurable fun a => p a -> q a
  proof: measurableSet_setOfPred.1 hp.setOf.himp hq.setOf

@[fun_prop]

中文:
引理 Measurable.imp
  条件: (hp : Measurable p) (hq : Measurable q)
  结论: Measurable fun a => p a -> q a
  证明: measurableSet_setOfPred.1 hp.setOf.himp hq.setOf

@[fun_prop]

Depends on / 依赖: hp.setOf.himp, hq.setOf, measurableSet_setOfPred
-/
lemma Measurable.imp (hp : Measurable p) (hq : Measurable q) : Measurable fun a => p a -> q a :=
measurableSet_setOfPred.1 hp.setOf.himp hq.setOf

@[fun_prop]
/--
lemma `Measurable.iff` / 引理 `Measurable.iff`

English:
lemma Measurable.iff
  given: (hp : Measurable p) (hq : Measurable q)
  statement: Measurable fun a => p a ↔ q a
  proof: measurableSet_setOfPred.1 by
    simp_rw [iff_iff_implies_and_implies]; exact hq.setOf.bihimp hp.setOf

@[fun_prop]

中文:
引理 Measurable.iff
  条件: (hp : Measurable p) (hq : Measurable q)
  结论: Measurable fun a => p a ↔ q a
  证明: measurableSet_setOfPred.1 by
    simp_rw [iff_iff_implies_and_implies]; exact hq.setOf.bihimp hp.setOf

@[fun_prop]

Depends on / 依赖: bihimp, hp.setOf, hq.setOf.bihimp, iff_iff_implies_and_implies, measurableSet_setOfPred, simp_rw
-/
lemma Measurable.iff (hp : Measurable p) (hq : Measurable q) : Measurable fun a => p a ↔ q a :=
measurableSet_setOfPred.1 by
    simp_rw [iff_iff_implies_and_implies]; exact hq.setOf.bihimp hp.setOf

@[fun_prop]
/--
lemma `Measurable.forall` / 引理 `Measurable.forall`

English:
lemma Measurable.forall
  given: [Countable ι] {p : ι -> α -> Prop} (hp : forall i, Measurable (p i))
  proof: measurableSet_setOfPred.1 by
    rw [ofPred_forall]; exact MeasurableSet.iInter fun i => (hp i).setOf

@[fun_prop]

中文:
引理 Measurable.forall
  条件: [Countable ι] {p : ι -> α -> 命题} (hp : 对任意 i, Measurable (p i))
  证明: measurableSet_setOfPred.1 by
    rw [ofPred_forall]; exact MeasurableSet.iInter fun i => (hp i).setOf

@[fun_prop]

Depends on / 依赖: MeasurableSet, MeasurableSet.iInter, iInter, measurableSet_setOfPred, ofPred_forall
-/
lemma Measurable.forall [Countable ι] {p : ι -> α -> Prop} (hp : forall i, Measurable (p i)) :
    Measurable fun a => forall i, p i a :=
measurableSet_setOfPred.1 by
    rw [ofPred_forall]; exact MeasurableSet.iInter fun i => (hp i).setOf

@[fun_prop]
/--
lemma `Measurable.exists` / 引理 `Measurable.exists`

English:
lemma Measurable.exists
  given: [Countable ι] {p : ι -> α -> Prop} (hp : forall i, Measurable (p i))
  proof: measurableSet_setOfPred.1 by
    rw [ofPred_exists]; exact MeasurableSet.iUnion fun i => (hp i).setOf

中文:
引理 Measurable.exists
  条件: [Countable ι] {p : ι -> α -> 命题} (hp : 对任意 i, Measurable (p i))
  证明: measurableSet_setOfPred.1 by
    rw [ofPred_exists]; exact MeasurableSet.iUnion fun i => (hp i).setOf

Depends on / 依赖: MeasurableSet, MeasurableSet.iUnion, iUnion, measurableSet_setOfPred, ofPred_exists
-/
lemma Measurable.exists [Countable ι] {p : ι -> α -> Prop} (hp : forall i, Measurable (p i)) :
    Measurable fun a => exists i, p i a :=
measurableSet_setOfPred.1 by
    rw [ofPred_exists]; exact MeasurableSet.iUnion fun i => (hp i).setOf

end prop

@[fun_prop]
/--
lemma `Measurable.eq_const` / 引理 `Measurable.eq_const`

English:
lemma Measurable.eq_const
  statement: {_ : MeasurableSpace α} [MeasurableSpace β] [MeasurableSingletonClass β]
  proof: measurableSet_setOfPred.mp (measurableSet_eq.preimage hf)

@[fun_prop]

中文:
引理 Measurable.eq_const
  结论: {_ : MeasurableSpace α} [MeasurableSpace β] [MeasurableSingletonClass β]
  证明: measurableSet_setOfPred.mp (measurableSet_eq.preimage hf)

@[fun_prop]

Depends on / 依赖: measurableSet_eq, measurableSet_eq.preimage, measurableSet_setOfPred, measurableSet_setOfPred.mp, preimage
-/
lemma Measurable.eq_const {_ : MeasurableSpace α} [MeasurableSpace β] [MeasurableSingletonClass β]
    {f : α -> β} (hf : Measurable f) (a : β) : Measurable fun x => f x = a :=
  measurableSet_setOfPred.mp (measurableSet_eq.preimage hf)

@[fun_prop]
/--
lemma `Measurable.const_eq` / 引理 `Measurable.const_eq`

English:
lemma Measurable.const_eq
  statement: {_ : MeasurableSpace α} [MeasurableSpace β] [MeasurableSingletonClass β]
  proof: by
  conv => enter [1, x]; rw [eq_comm]
  exact .eq_const hf a

中文:
引理 Measurable.const_eq
  结论: {_ : MeasurableSpace α} [MeasurableSpace β] [MeasurableSingletonClass β]
  证明: by
  conv => enter [1, x]; rw [eq_comm]
  exact .eq_const hf a

Depends on / 依赖: eq_comm, eq_const
-/
lemma Measurable.const_eq {_ : MeasurableSpace α} [MeasurableSpace β] [MeasurableSingletonClass β]
    {f : α -> β} (hf : Measurable f) (a : β) : Measurable fun x => a = f x := by
  conv => enter [1, x]; rw [eq_comm]
  exact .eq_const hf a

section Set
variable [MeasurableSpace β] {g : β -> Set α}

/--
Instance `Set.instMeasurableSpace` / 实例 `Set.instMeasurableSpace`

English:
instance Set.instMeasurableSpace
  signature: : MeasurableSpace (Set α)
  body: inferInstanceAs MeasurableSpace (α -> Prop)

中文:
实例 Set.instMeasurableSpace
  签名: : MeasurableSpace (Set α)
  定义体: inferInstanceAs MeasurableSpace (α -> Prop)

Depends on / 依赖: MeasurableSpace
-/
instance Set.instMeasurableSpace : MeasurableSpace (Set α) :=
inferInstanceAs MeasurableSpace (α -> Prop)

/--
Instance `Set.instMeasurableSingletonClass` / 实例 `Set.instMeasurableSingletonClass`

English:
instance Set.instMeasurableSingletonClass
  signature: [Countable α]
  body: inferInstanceAs MeasurableSingletonClass (α -> Prop)

中文:
实例 Set.instMeasurableSingletonClass
  签名: [Countable α]
  定义体: inferInstanceAs MeasurableSingletonClass (α -> Prop)

Depends on / 依赖: MeasurableSingletonClass
-/
instance Set.instMeasurableSingletonClass [Countable α] : MeasurableSingletonClass (Set α) :=
inferInstanceAs MeasurableSingletonClass (α -> Prop)

/--
lemma `measurable_setOfPred` / 引理 `measurable_setOfPred`

English:
lemma measurable_setOfPred
  proof: measurable_id

@[deprecated (since := "2026-07-09")]
alias measurable_setOf := measurable_setOfPred

中文:
引理 measurable_setOfPred
  证明: measurable_id

@[deprecated (since := "2026-07-09")]
alias measurable_setOf := measurable_setOfPred
-/
@[simp, fun_prop] lemma measurable_setOfPred :
    Measurable fun p : α -> Prop => {a | p a} := measurable_id

@[deprecated (since := "2026-07-09")]
alias measurable_setOf := measurable_setOfPred

/--
lemma `measurable_set_iff` / 引理 `measurable_set_iff`

English:
lemma measurable_set_iff
  statement: Measurable g ↔ forall a, Measurable fun x => a in g x
  proof: measurable_pi_iff

@[fun_prop]

中文:
引理 measurable_set_iff
  结论: Measurable g ↔ 对任意 a, Measurable fun x => a in g x
  证明: measurable_pi_iff

@[fun_prop]

Depends on / 依赖: measurable_pi_iff
-/
lemma measurable_set_iff : Measurable g ↔ forall a, Measurable fun x => a in g x := measurable_pi_iff

@[fun_prop]
/--
lemma `measurable_set_mem` / 引理 `measurable_set_mem`

English:
lemma measurable_set_mem
  given: (a : α)
  statement: Measurable fun s : Set α => a in s
  proof: measurable_pi_apply _

中文:
引理 measurable_set_mem
  条件: (a : α)
  结论: Measurable fun s : Set α => a in s
  证明: measurable_pi_apply _

Depends on / 依赖: measurable_pi_apply
-/
lemma measurable_set_mem (a : α) : Measurable fun s : Set α => a in s := measurable_pi_apply _

/--
lemma `measurable_set_notMem` / 引理 `measurable_set_notMem`

English:
lemma measurable_set_notMem
  given: (a : α)
  statement: Measurable fun s : Set α => a ∉ s
  proof: (Measurable.of_discrete (f := Not)).comp measurable_set_mem a

中文:
引理 measurable_set_notMem
  条件: (a : α)
  结论: Measurable fun s : Set α => a ∉ s
  证明: (Measurable.of_discrete (f := Not)).comp measurable_set_mem a

Depends on / 依赖: Measurable, Measurable.of_discrete, measurable_set_mem, of_discrete
-/
lemma measurable_set_notMem (a : α) : Measurable fun s : Set α => a ∉ s :=
(Measurable.of_discrete (f := Not)).comp measurable_set_mem a

/--
lemma `measurableSet_mem` / 引理 `measurableSet_mem`

English:
lemma measurableSet_mem
  given: (a : α)
  statement: MeasurableSet {s : Set α | a in s}
  proof: measurableSet_setOfPred.2 measurable_set_mem _

中文:
引理 measurableSet_mem
  条件: (a : α)
  结论: MeasurableSet {s : Set α | a in s}
  证明: measurableSet_setOfPred.2 measurable_set_mem _

Depends on / 依赖: measurableSet_setOfPred, measurable_set_mem
-/
lemma measurableSet_mem (a : α) : MeasurableSet {s : Set α | a in s} :=
measurableSet_setOfPred.2 measurable_set_mem _

/--
lemma `measurableSet_notMem` / 引理 `measurableSet_notMem`

English:
lemma measurableSet_notMem
  given: (a : α)
  statement: MeasurableSet {s : Set α | a ∉ s}
  proof: measurableSet_setOfPred.2 measurable_set_notMem _

中文:
引理 measurableSet_notMem
  条件: (a : α)
  结论: MeasurableSet {s : Set α | a ∉ s}
  证明: measurableSet_setOfPred.2 measurable_set_notMem _

Depends on / 依赖: measurableSet_setOfPred, measurable_set_notMem
-/
lemma measurableSet_notMem (a : α) : MeasurableSet {s : Set α | a ∉ s} :=
measurableSet_setOfPred.2 measurable_set_notMem _

/--
lemma `measurable_compl` / 引理 `measurable_compl`

English:
lemma measurable_compl
  statement: Measurable ((·ᶜ) : Set α -> Set α)
  proof: measurable_set_iff.2 fun _ => measurable_set_notMem _

中文:
引理 measurable_compl
  结论: Measurable ((·ᶜ) : Set α -> Set α)
  证明: measurable_set_iff.2 fun _ => measurable_set_notMem _

Depends on / 依赖: measurable_set_iff, measurable_set_notMem
-/
lemma measurable_compl : Measurable ((·ᶜ) : Set α -> Set α) :=
  measurable_set_iff.2 fun _ => measurable_set_notMem _

variable [Countable α]

/--
lemma `MeasurableSet.setOfPred_finite` / 引理 `MeasurableSet.setOfPred_finite`

English:
lemma MeasurableSet.setOfPred_finite
  statement: MeasurableSet {s : Set α | s.Finite}
  proof: Countable.ofPred_finite.measurableSet

@[deprecated (since := "2026-07-09")]
alias MeasurableSet.setOf_finite := MeasurableSet.setOfPred_finite

中文:
引理 MeasurableSet.setOfPred_finite
  结论: MeasurableSet {s : Set α | s.Finite}
  证明: Countable.ofPred_finite.measurableSet

@[deprecated (since := "2026-07-09")]
alias MeasurableSet.setOf_finite := MeasurableSet.setOfPred_finite

Depends on / 依赖: Countable, Countable.ofPred_finite.measurableSet, measurableSet, ofPred_finite
-/
lemma MeasurableSet.setOfPred_finite : MeasurableSet {s : Set α | s.Finite} :=
  Countable.ofPred_finite.measurableSet

@[deprecated (since := "2026-07-09")]
alias MeasurableSet.setOf_finite := MeasurableSet.setOfPred_finite

/--
lemma `MeasurableSet.setOfPred_infinite` / 引理 `MeasurableSet.setOfPred_infinite`

English:
lemma MeasurableSet.setOfPred_infinite
  statement: MeasurableSet {s : Set α | s.Infinite}
  proof: .compl .setOfPred_finite

@[deprecated (since := "2026-07-09")]
alias MeasurableSet.setOf_infinite := MeasurableSet.setOfPred_infinite

中文:
引理 MeasurableSet.setOfPred_infinite
  结论: MeasurableSet {s : Set α | s.Infinite}
  证明: .compl .setOfPred_finite

@[deprecated (since := "2026-07-09")]
alias MeasurableSet.setOf_infinite := MeasurableSet.setOfPred_infinite

Depends on / 依赖: setOfPred_finite
-/
lemma MeasurableSet.setOfPred_infinite : MeasurableSet {s : Set α | s.Infinite} :=
.compl .setOfPred_finite

@[deprecated (since := "2026-07-09")]
alias MeasurableSet.setOf_infinite := MeasurableSet.setOfPred_infinite

/--
lemma `MeasurableSet.sep_finite` / 引理 `MeasurableSet.sep_finite`

English:
lemma MeasurableSet.sep_finite
  given: {S : Set (Set α)} (hS : MeasurableSet S)
  proof: hS.inter .setOfPred_finite

中文:
引理 MeasurableSet.sep_finite
  条件: {S : Set (Set α)} (hS : MeasurableSet S)
  证明: hS.inter .setOfPred_finite

Depends on / 依赖: hS.inter, setOfPred_finite
-/
lemma MeasurableSet.sep_finite {S : Set (Set α)} (hS : MeasurableSet S) :
    MeasurableSet {s in S | s.Finite} :=
  hS.inter .setOfPred_finite

/--
lemma `MeasurableSet.sep_infinite` / 引理 `MeasurableSet.sep_infinite`

English:
lemma MeasurableSet.sep_infinite
  given: {S : Set (Set α)} (hS : MeasurableSet S)
  proof: hS.inter .setOfPred_infinite

@[fun_prop]

中文:
引理 MeasurableSet.sep_infinite
  条件: {S : Set (Set α)} (hS : MeasurableSet S)
  证明: hS.inter .setOfPred_infinite

@[fun_prop]

Depends on / 依赖: hS.inter, setOfPred_infinite
-/
lemma MeasurableSet.sep_infinite {S : Set (Set α)} (hS : MeasurableSet S) :
    MeasurableSet {s in S | s.Infinite} :=
  hS.inter .setOfPred_infinite

@[fun_prop]
/--
lemma `Measurable.subset` / 引理 `Measurable.subset`

English:
lemma Measurable.subset
  given: {s t : β -> Set α} (hs : Measurable s) (hs : Measurable t)
  proof: .forall fun i => .imp (by fun_prop) (by fun_prop)

中文:
引理 Measurable.subset
  条件: {s t : β -> Set α} (hs : Measurable s) (hs : Measurable t)
  证明: .forall fun i => .imp (by fun_prop) (by fun_prop)
-/
protected lemma Measurable.subset {s t : β -> Set α} (hs : Measurable s) (hs : Measurable t) :
    Measurable fun a => s a subseteq t a :=
  .forall fun i => .imp (by fun_prop) (by fun_prop)

end Set

section Finset
variable [MeasurableSpace β] {g : β -> Finset α}

/--
Instance `Finset.instMeasurableSpace` / 实例 `Finset.instMeasurableSpace`

English:
instance Finset.instMeasurableSpace
  signature: : MeasurableSpace (Finset α)
  body: .comap SetLike.coe inferInstance

中文:
实例 Finset.instMeasurableSpace
  签名: : MeasurableSpace (Finset α)
  定义体: .comap SetLike.coe inferInstance

Depends on / 依赖: SetLike, SetLike.coe
-/
instance Finset.instMeasurableSpace : MeasurableSpace (Finset α) :=
  .comap SetLike.coe inferInstance

/--
lemma `measurable_finset_iff_measurable_set` / 引理 `measurable_finset_iff_measurable_set`

English:
lemma measurable_finset_iff_measurable_set
  statement: Measurable g ↔ Measurable (fun x => (g x : Set α))
  proof: measurable_comap_iff

中文:
引理 measurable_finset_iff_measurable_set
  结论: Measurable g ↔ Measurable (fun x => (g x : Set α))
  证明: measurable_comap_iff

Depends on / 依赖: measurable_comap_iff
-/
lemma measurable_finset_iff_measurable_set : Measurable g ↔ Measurable (fun x => (g x : Set α)) :=
  measurable_comap_iff

/--
lemma `measurable_finset_iff` / 引理 `measurable_finset_iff`

English:
lemma measurable_finset_iff
  statement: Measurable g ↔ forall a, Measurable (a in g ·)
  proof: by
  rw [measurable_finset_iff_measurable_set]; rw [measurable_set_iff]; rfl

中文:
引理 measurable_finset_iff
  结论: Measurable g ↔ 对任意 a, Measurable (a in g ·)
  证明: by
  rw [measurable_finset_iff_measurable_set]; rw [measurable_set_iff]; rfl

Depends on / 依赖: measurable_finset_iff_measurable_set, measurable_set_iff
-/
lemma measurable_finset_iff : Measurable g ↔ forall a, Measurable (a in g ·) := by
  rw [measurable_finset_iff_measurable_set]; rw [measurable_set_iff]; rfl

/--
lemma `measurableSet_finset_iff` / 引理 `measurableSet_finset_iff`

English:
lemma measurableSet_finset_iff
  given: (S : Set (Finset α))
  statement: MeasurableSet S ↔
  proof: MeasurableSpace.measurableSet_comap

@[fun_prop]

中文:
引理 measurableSet_finset_iff
  条件: (S : Set (Finset α))
  结论: MeasurableSet S ↔
  证明: MeasurableSpace.measurableSet_comap

@[fun_prop]

Depends on / 依赖: MeasurableSpace, MeasurableSpace.measurableSet_comap, measurableSet_comap
-/
lemma measurableSet_finset_iff (S : Set (Finset α)) : MeasurableSet S ↔
    exists S' : Set (Set α), MeasurableSet S' ∧ { s : Finset α | ↑s in S'} = S :=
  MeasurableSpace.measurableSet_comap

@[fun_prop]
/--
lemma `measurable_finset_mem` / 引理 `measurable_finset_mem`

English:
lemma measurable_finset_mem
  given: (a : α)
  statement: Measurable fun s : Finset α => a in s
  proof: (measurable_set_mem a).comp (comap_measurable _)

中文:
引理 measurable_finset_mem
  条件: (a : α)
  结论: Measurable fun s : Finset α => a in s
  证明: (measurable_set_mem a).comp (comap_measurable _)

Depends on / 依赖: comap_measurable, measurable_set_mem
-/
lemma measurable_finset_mem (a : α) : Measurable fun s : Finset α => a in s :=
  (measurable_set_mem a).comp (comap_measurable _)

/--
lemma `measurable_finset_notMem` / 引理 `measurable_finset_notMem`

English:
lemma measurable_finset_notMem
  given: (a : α)
  statement: Measurable fun s : Finset α => a ∉ s
  proof: (measurable_set_notMem a).comp (comap_measurable _)

中文:
引理 measurable_finset_notMem
  条件: (a : α)
  结论: Measurable fun s : Finset α => a ∉ s
  证明: (measurable_set_notMem a).comp (comap_measurable _)

Depends on / 依赖: comap_measurable, measurable_set_notMem
-/
lemma measurable_finset_notMem (a : α) : Measurable fun s : Finset α => a ∉ s :=
  (measurable_set_notMem a).comp (comap_measurable _)

/--
lemma `measurableSet_mem_finset` / 引理 `measurableSet_mem_finset`

English:
lemma measurableSet_mem_finset
  given: (a : α)
  statement: MeasurableSet {s : Finset α | a in s}
  proof: measurableSet_setOfPred.2 measurable_finset_mem _

中文:
引理 measurableSet_mem_finset
  条件: (a : α)
  结论: MeasurableSet {s : Finset α | a in s}
  证明: measurableSet_setOfPred.2 measurable_finset_mem _

Depends on / 依赖: measurableSet_setOfPred, measurable_finset_mem
-/
lemma measurableSet_mem_finset (a : α) : MeasurableSet {s : Finset α | a in s} :=
measurableSet_setOfPred.2 measurable_finset_mem _

/--
lemma `measurableSet_notMem_finset` / 引理 `measurableSet_notMem_finset`

English:
lemma measurableSet_notMem_finset
  given: (a : α)
  statement: MeasurableSet {s : Finset α | a ∉ s}
  proof: measurableSet_setOfPred.2 measurable_finset_notMem _

中文:
引理 measurableSet_notMem_finset
  条件: (a : α)
  结论: MeasurableSet {s : Finset α | a ∉ s}
  证明: measurableSet_setOfPred.2 measurable_finset_notMem _

Depends on / 依赖: measurableSet_setOfPred, measurable_finset_notMem
-/
lemma measurableSet_notMem_finset (a : α) : MeasurableSet {s : Finset α | a ∉ s} :=
measurableSet_setOfPred.2 measurable_finset_notMem _

variable [Countable α]

/--
Instance `Finset.instMeasurableSingletonClass` / 实例 `Finset.instMeasurableSingletonClass`

English:
instance Finset.instMeasurableSingletonClass
  signature: : MeasurableSingletonClass (Finset α)
  body: .mk fun S => (measurableSet_finset_iff _).mpr ⟨{↑S}, by simp, by ext; simp⟩

中文:
实例 Finset.instMeasurableSingletonClass
  签名: : MeasurableSingletonClass (Finset α)
  定义体: .mk fun S => (measurableSet_finset_iff _).mpr ⟨{↑S}, by simp, by ext; simp⟩

Depends on / 依赖: measurableSet_finset_iff
-/
instance Finset.instMeasurableSingletonClass : MeasurableSingletonClass (Finset α) :=
  .mk fun S => (measurableSet_finset_iff _).mpr ⟨{↑S}, by simp, by ext; simp⟩

end Finset

section curry

variable {ι : Type*}

section Function

variable {κ X : Type*} [MeasurableSpace X]

@[fun_prop]
/--
lemma `measurable_curry` / 引理 `measurable_curry`

English:
lemma measurable_curry
  statement: Measurable (@curry ι κ X)
  proof: measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _

中文:
引理 measurable_curry
  结论: Measurable (@curry ι κ X)
  证明: measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _

Depends on / 依赖: measurable_pi_apply, measurable_pi_lambda
-/
lemma measurable_curry : Measurable (@curry ι κ X) :=
  measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _

-- This cannot be tagged with `fun_prop` because `fun_prop` can see through `Function.uncurry`.
/--
lemma `measurable_uncurry` / 引理 `measurable_uncurry`

English:
lemma measurable_uncurry
  statement: Measurable (@uncurry ι κ X)
  proof: by fun_prop

@[fun_prop]

中文:
引理 measurable_uncurry
  结论: Measurable (@uncurry ι κ X)
  证明: by fun_prop

@[fun_prop]

Depends on / 依赖: fun_prop
-/
lemma measurable_uncurry : Measurable (@uncurry ι κ X) := by fun_prop

@[fun_prop]
/--
lemma `measurable_equivCurry` / 引理 `measurable_equivCurry`

English:
lemma measurable_equivCurry
  statement: Measurable (Equiv.curry ι κ X)
  proof: measurable_curry

@[fun_prop]

中文:
引理 measurable_equivCurry
  结论: Measurable (Equiv.curry ι κ X)
  证明: measurable_curry

@[fun_prop]

Depends on / 依赖: measurable_curry
-/
lemma measurable_equivCurry : Measurable (Equiv.curry ι κ X) := measurable_curry

@[fun_prop]
/--
lemma `measurable_equivCurry_symm` / 引理 `measurable_equivCurry_symm`

English:
lemma measurable_equivCurry_symm
  statement: Measurable (Equiv.curry ι κ X).symm
  proof: measurable_uncurry

中文:
引理 measurable_equivCurry_symm
  结论: Measurable (Equiv.curry ι κ X).symm
  证明: measurable_uncurry

Depends on / 依赖: measurable_uncurry
-/
lemma measurable_equivCurry_symm : Measurable (Equiv.curry ι κ X).symm := measurable_uncurry

end Function

section Sigma

variable {κ : ι -> Type*} {X : (i : ι) -> κ i -> Type*} [forall i j, MeasurableSpace (X i j)]

@[fun_prop]
/--
lemma `measurable_sigmaCurry` / 引理 `measurable_sigmaCurry`

English:
lemma measurable_sigmaCurry
  statement: Measurable (Sigma.curry (γ := X))
  proof: measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]

中文:
引理 measurable_sigmaCurry
  结论: Measurable (Sigma.curry (γ := X))
  证明: measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]
-/
lemma measurable_sigmaCurry : Measurable (Sigma.curry (γ := X)) :=
    measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ => measurable_pi_apply _

@[fun_prop]
/--
lemma `measurable_sigmaUncurry` / 引理 `measurable_sigmaUncurry`

English:
lemma measurable_sigmaUncurry
  statement: Measurable (Sigma.uncurry (γ := X))
  proof: by
  refine measurable_pi_lambda _ fun _ => ?_
  simp only [Sigma.uncurry]
  fun_prop

@[fun_prop]

中文:
引理 measurable_sigmaUncurry
  结论: Measurable (Sigma.uncurry (γ := X))
  证明: by
  refine measurable_pi_lambda _ fun _ => ?_
  simp only [Sigma.uncurry]
  fun_prop

@[fun_prop]

Depends on / 依赖: Sigma.uncurry, fun_prop, measurable_pi_lambda, uncurry
-/
lemma measurable_sigmaUncurry : Measurable (Sigma.uncurry (γ := X)) := by
  refine measurable_pi_lambda _ fun _ => ?_
  simp only [Sigma.uncurry]
  fun_prop

@[fun_prop]
/--
lemma `measurable_piCurry` / 引理 `measurable_piCurry`

English:
lemma measurable_piCurry
  statement: Measurable (Equiv.piCurry X)
  proof: measurable_sigmaCurry

@[fun_prop]

中文:
引理 measurable_piCurry
  结论: Measurable (Equiv.piCurry X)
  证明: measurable_sigmaCurry

@[fun_prop]

Depends on / 依赖: measurable_sigmaCurry
-/
lemma measurable_piCurry : Measurable (Equiv.piCurry X) := measurable_sigmaCurry

@[fun_prop]
/--
lemma `measurable_piCurry_symm` / 引理 `measurable_piCurry_symm`

English:
lemma measurable_piCurry_symm
  statement: Measurable (Equiv.piCurry X).symm
  proof: measurable_sigmaUncurry

中文:
引理 measurable_piCurry_symm
  结论: Measurable (Equiv.piCurry X).symm
  证明: measurable_sigmaUncurry

Depends on / 依赖: measurable_sigmaUncurry
-/
lemma measurable_piCurry_symm : Measurable (Equiv.piCurry X).symm := measurable_sigmaUncurry

end Sigma

end curry

variable (α) in
/--
Definition of `MeasurableEq` / `MeasurableEq` 的定义

English:
class MeasurableEq
  parameters: [MeasurableSpace α]
  axioms and operations (1):
    - measurableSet_diagonal : MeasurableSet (diagonal α)

中文:
类 MeasurableEq
  参数: [MeasurableSpace α]
  公理与运算 (1 个):
    - measurableSet_diagonal : MeasurableSet (diagonal α)
-/
class MeasurableEq [MeasurableSpace α] where
  measurableSet_diagonal : MeasurableSet (diagonal α)

export MeasurableEq (measurableSet_diagonal)

attribute [measurability] measurableSet_diagonal

/--
theorem `measurableSet_eq_fun` / 定理 `measurableSet_eq_fun`

English:
theorem measurableSet_eq_fun
  statement: {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]
  proof: measurableSet_diagonal.preimage (hf.prodMk hg)

@[fun_prop]

中文:
定理 measurableSet_eq_fun
  结论: {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]
  证明: measurableSet_diagonal.preimage (hf.prodMk hg)

@[fun_prop]

Depends on / 依赖: hf.prodMk, measurableSet_diagonal, measurableSet_diagonal.preimage, preimage, prodMk
-/
theorem measurableSet_eq_fun {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]
    {f g : α -> β} (hf : Measurable f) (hg : Measurable g) : MeasurableSet {x | f x = g x} :=
  measurableSet_diagonal.preimage (hf.prodMk hg)

@[fun_prop]
/--
theorem `Measurable.eq` / 定理 `Measurable.eq`

English:
theorem Measurable.eq
  statement: {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]
  proof: measurableSet_setOfPred.mp (measurableSet_eq_fun hf hg)

中文:
定理 Measurable.eq
  结论: {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]
  证明: measurableSet_setOfPred.mp (measurableSet_eq_fun hf hg)

Depends on / 依赖: measurableSet_eq_fun, measurableSet_setOfPred, measurableSet_setOfPred.mp
-/
theorem Measurable.eq {m : MeasurableSpace α} [MeasurableSpace β] [MeasurableEq β]
    {f g : α -> β} (hf : Measurable f) (hg : Measurable g) : Measurable fun x => f x = g x :=
  measurableSet_setOfPred.mp (measurableSet_eq_fun hf hg)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MeasurableSpace
  signature: α] [MeasurableEq α] : MeasurableSingletonClass α
  body: by
  constructor
  simp_rw [← ofPred_eq_eq_singleton, measurableSet_setOfPred]
  measurability

中文:
实例 [MeasurableSpace
  签名: α] [MeasurableEq α] : MeasurableSingletonClass α
  定义体: by
  constructor
  simp_rw [← ofPred_eq_eq_singleton, measurableSet_setOfPred]
  measurability

Depends on / 依赖: measurability, measurableSet_setOfPred, ofPred_eq_eq_singleton, simp_rw
-/
instance [MeasurableSpace α] [MeasurableEq α] : MeasurableSingletonClass α := by
  constructor
  simp_rw [← ofPred_eq_eq_singleton, measurableSet_setOfPred]
  measurability

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [MeasurableSpace
  signature: α] [MeasurableSingletonClass α] [Countable α] : MeasurableEq α
  body: by
  constructor
  simp_rw [← Set.range_diag, Set.range_eq_iUnion]
  measurability

中文:
实例 [MeasurableSpace
  签名: α] [MeasurableSingletonClass α] [Countable α] : MeasurableEq α
  定义体: by
  constructor
  simp_rw [← Set.range_diag, Set.range_eq_iUnion]
  measurability

Depends on / 依赖: Set.range_diag, Set.range_eq_iUnion, measurability, range_diag, range_eq_iUnion, simp_rw
-/
instance [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] : MeasurableEq α := by
  constructor
  simp_rw [← Set.range_diag, Set.range_eq_iUnion]
  measurability
