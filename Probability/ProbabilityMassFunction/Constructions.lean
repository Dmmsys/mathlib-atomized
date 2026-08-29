/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Devon Tuma
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Control.ULiftable

/-!
# Specific Constructions of Probability Mass Functions

This file gives a number of different `PMF` constructions for common probability distributions.

`map` and `seq` allow pushing a `PMF α` along a function `f : α → β` (or distribution of
functions `f : PMF (α → β)`) to get a `PMF β`.

`ofFinset` and `ofFintype` simplify the construction of a `PMF α` from a function `f : α → ℝ≥0∞`,
by allowing the "sum equals 1" constraint to be in terms of `Finset.sum` instead of `tsum`.

`normalize` constructs a `PMF α` by normalizing a function `f : α → ℝ≥0∞` by its sum,
and `filter` uses this to filter the support of a `PMF` and re-normalize the new distribution.

`bernoulli` represents the Bernoulli distribution on `Bool`.

-/

@[expose] public section

universe u v

namespace PMF

noncomputable section

variable {α β γ : Type*}

open NNReal ENNReal Finset MeasureTheory

section Map

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (p : PMF α)
  body: bind p (pure ∘ f)

中文:
定义 map
  签名: (f : α -> β) (p : PMF α)
  定义体: bind p (pure ∘ f)
-/
def map (f : α -> β) (p : PMF α) : PMF β :=
  bind p (pure ∘ f)

variable (f : α -> β) (p : PMF α) (b : β)

/--
theorem `monad_map_eq_map` / 定理 `monad_map_eq_map`

English:
theorem monad_map_eq_map
  given: {α β : Type u} (f : α -> β) (p : PMF α)
  statement: f < > p = p.map f
  proof: rfl

中文:
定理 monad_map_eq_map
  条件: {α β : 类型u} (f : α -> β) (p : PMF α)
  结论: f < > p = p.map f
  证明: rfl
-/
theorem monad_map_eq_map {α β : Type u} (f : α -> β) (p : PMF α) : f < > p = p.map f := rfl

open scoped Classical in
@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  statement: (map f p) b = ∑' a, if b = f a then p a else 0
  proof: by simp [map]

@[simp]

中文:
定理 map_apply
  结论: (map f p) b = ∑' a, if b = f a then p a else 0
  证明: by simp [map]

@[simp]
-/
theorem map_apply : (map f p) b = ∑' a, if b = f a then p a else 0 := by simp [map]

@[simp]
/--
theorem `support_map` / 定理 `support_map`

English:
theorem support_map
  statement: (map f p).support = f '' p.support
  proof: Set.ext fun b => by simp [map, @eq_comm β b]

中文:
定理 support_map
  结论: (map f p).support = f '' p.support
  证明: Set.ext fun b => by simp [map, @eq_comm β b]

Depends on / 依赖: Set.ext, eq_comm
-/
theorem support_map : (map f p).support = f '' p.support :=
  Set.ext fun b => by simp [map, @eq_comm β b]

/--
theorem `mem_support_map_iff` / 定理 `mem_support_map_iff`

English:
theorem mem_support_map_iff
  statement: b in (map f p).support ↔ exists a in p.support, f a = b
  proof: by simp

中文:
定理 mem_support_map_iff
  结论: b in (map f p).support ↔ 存在 a in p.support, f a = b
  证明: by simp
-/
theorem mem_support_map_iff : b in (map f p).support ↔ exists a in p.support, f a = b := by simp

/--
theorem `bind_pure_comp` / 定理 `bind_pure_comp`

English:
theorem bind_pure_comp
  statement: bind p (pure ∘ f) = map f p
  proof: rfl

中文:
定理 bind_pure_comp
  结论: bind p (pure ∘ f) = map f p
  证明: rfl
-/
theorem bind_pure_comp : bind p (pure ∘ f) = map f p := rfl

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map id p = p
  proof: bind_pure _

中文:
定理 map_id
  结论: map id p = p
  证明: bind_pure _

Depends on / 依赖: bind_pure
-/
theorem map_id : map id p = p :=
  bind_pure _

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  given: (g : β -> γ)
  statement: (p.map f).map g = p.map (g ∘ f)
  proof: by simp [map, Function.comp_def]

中文:
定理 map_comp
  条件: (g : β -> γ)
  结论: (p.map f).map g = p.map (g ∘ f)
  证明: by simp [map, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def
-/
theorem map_comp (g : β -> γ) : (p.map f).map g = p.map (g ∘ f) := by simp [map, Function.comp_def]

/--
theorem `pure_map` / 定理 `pure_map`

English:
theorem pure_map
  given: (a : α)
  statement: (pure a).map f = pure (f a)
  proof: pure_bind _ _

中文:
定理 pure_map
  条件: (a : α)
  结论: (pure a).map f = pure (f a)
  证明: pure_bind _ _

Depends on / 依赖: pure_bind
-/
theorem pure_map (a : α) : (pure a).map f = pure (f a) :=
  pure_bind _ _

/--
theorem `map_bind` / 定理 `map_bind`

English:
theorem map_bind
  given: (q : α -> PMF β) (f : β -> γ)
  statement: (p.bind q).map f = p.bind fun a => (q a).map f
  proof: bind_bind _ _ _

@[simp]

中文:
定理 map_bind
  条件: (q : α -> PMF β) (f : β -> γ)
  结论: (p.bind q).map f = p.bind fun a => (q a).map f
  证明: bind_bind _ _ _

@[simp]

Depends on / 依赖: bind_bind
-/
theorem map_bind (q : α -> PMF β) (f : β -> γ) : (p.bind q).map f = p.bind fun a => (q a).map f :=
  bind_bind _ _ _

@[simp]
/--
theorem `bind_map` / 定理 `bind_map`

English:
theorem bind_map
  given: (p : PMF α) (f : α -> β) (q : β -> PMF γ)
  statement: (p.map f).bind q = p.bind (q ∘ f)
  proof: (bind_bind _ _ _).trans (congr_arg _ (funext fun _ => pure_bind _ _))

@[simp]

中文:
定理 bind_map
  条件: (p : PMF α) (f : α -> β) (q : β -> PMF γ)
  结论: (p.map f).bind q = p.bind (q ∘ f)
  证明: (bind_bind _ _ _).trans (congr_arg _ (funext fun _ => pure_bind _ _))

@[simp]

Depends on / 依赖: bind_bind, congr_arg, pure_bind
-/
theorem bind_map (p : PMF α) (f : α -> β) (q : β -> PMF γ) : (p.map f).bind q = p.bind (q ∘ f) :=
  (bind_bind _ _ _).trans (congr_arg _ (funext fun _ => pure_bind _ _))

@[simp]
/--
theorem `map_const` / 定理 `map_const`

English:
theorem map_const
  statement: p.map (Function.const α b) = pure b
  proof: by
  simp only [map, Function.comp_def, bind_const, Function.const]

中文:
定理 map_const
  结论: p.map (Function.const α b) = pure b
  证明: by
  simp only [map, Function.comp_def, bind_const, Function.const]

Depends on / 依赖: Function, Function.comp_def, Function.const, bind_const, comp_def
-/
theorem map_const : p.map (Function.const α b) = pure b := by
  simp only [map, Function.comp_def, bind_const, Function.const]

section Measure

variable (s : Set β)

@[simp]
/--
theorem `toOuterMeasure_map_apply` / 定理 `toOuterMeasure_map_apply`

English:
theorem toOuterMeasure_map_apply
  statement: (p.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s)
  proof: by
  simp [map, Set.indicator, toOuterMeasure_apply p (f ⁻¹' s)]
  rfl

中文:
定理 toOuterMeasure_map_apply
  结论: (p.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s)
  证明: by
  simp [map, Set.indicator, toOuterMeasure_apply p (f ⁻¹' s)]
  rfl

Depends on / 依赖: Set.indicator, indicator, toOuterMeasure_apply
-/
theorem toOuterMeasure_map_apply : (p.map f).toOuterMeasure s = p.toOuterMeasure (f ⁻¹' s) := by
  simp [map, Set.indicator, toOuterMeasure_apply p (f ⁻¹' s)]
  rfl

variable {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

@[simp]
/--
theorem `toMeasure_map_apply` / 定理 `toMeasure_map_apply`

English:
theorem toMeasure_map_apply
  statement: (hf : Measurable f)
  proof: by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ hs]; rw [toMeasure_apply_eq_toOuterMeasure_apply _ (measurableSet_preimage hf hs)]
  exact toOuterMeasure_map_apply f p s

@[simp]

中文:
定理 toMeasure_map_apply
  结论: (hf : Measurable f)
  证明: by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ hs]; rw [toMeasure_apply_eq_toOuterMeasure_apply _ (measurableSet_preimage hf hs)]
  exact toOuterMeasure_map_apply f p s

@[simp]

Depends on / 依赖: measurableSet_preimage, toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_map_apply
-/
theorem toMeasure_map_apply (hf : Measurable f)
    (hs : MeasurableSet s) : (p.map f).toMeasure s = p.toMeasure (f ⁻¹' s) := by
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ hs]; rw [toMeasure_apply_eq_toOuterMeasure_apply _ (measurableSet_preimage hf hs)]
  exact toOuterMeasure_map_apply f p s

@[simp]
/--
lemma `toMeasure_map` / 引理 `toMeasure_map`

English:
lemma toMeasure_map
  given: (p : PMF α) (hf : Measurable f)
  statement: p.toMeasure.map f = (p.map f).toMeasure
  proof: by
  ext s hs : 1; rw [PMF.toMeasure_map_apply _ _ _ hf hs, Measure.map_apply hf hs]

中文:
引理 toMeasure_map
  条件: (p : PMF α) (hf : Measurable f)
  结论: p.toMeasure.map f = (p.map f).toMeasure
  证明: by
  ext s hs : 1; rw [PMF.toMeasure_map_apply _ _ _ hf hs, Measure.map_apply hf hs]

Depends on / 依赖: Measure, Measure.map_apply, PMF.toMeasure_map_apply, map_apply, toMeasure_map_apply
-/
lemma toMeasure_map (p : PMF α) (hf : Measurable f) : p.toMeasure.map f = (p.map f).toMeasure := by
  ext s hs : 1; rw [PMF.toMeasure_map_apply _ _ _ hf hs, Measure.map_apply hf hs]

end Measure

end Map

section Seq

/--
Definition of `seq` / `seq` 的定义

English:
definition seq
  signature: (q : PMF (α -> β)) (p : PMF α)
  body: q.bind fun m => p.bind fun a => pure (m a)

中文:
定义 seq
  签名: (q : PMF (α -> β)) (p : PMF α)
  定义体: q.bind fun m => p.bind fun a => pure (m a)

Depends on / 依赖: p.bind, q.bind
-/
def seq (q : PMF (α -> β)) (p : PMF α) : PMF β :=
  q.bind fun m => p.bind fun a => pure (m a)

variable (q : PMF (α -> β)) (p : PMF α) (b : β)

/--
theorem `monad_seq_eq_seq` / 定理 `monad_seq_eq_seq`

English:
theorem monad_seq_eq_seq
  given: {α β : Type u} (q : PMF (α -> β)) (p : PMF α)
  statement: q <*> p = q.seq p
  proof: rfl

中文:
定理 monad_seq_eq_seq
  条件: {α β : 类型u} (q : PMF (α -> β)) (p : PMF α)
  结论: q <*> p = q.seq p
  证明: rfl
-/
theorem monad_seq_eq_seq {α β : Type u} (q : PMF (α -> β)) (p : PMF α) : q <*> p = q.seq p := rfl

open scoped Classical in
@[simp]
/--
theorem `seq_apply` / 定理 `seq_apply`

English:
theorem seq_apply
  statement: (seq q p) b = ∑' (f : α -> β) (a : α), if b = f a then q f * p a else 0
  proof: by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine tsum_congr fun f => ENNReal.tsum_mul_left.symm.trans (tsum_congr fun a => ?_)
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (p a) 0

@[simp]

中文:
定理 seq_apply
  结论: (seq q p) b = ∑' (f : α -> β) (a : α), if b = f a then q f * p a else 0
  证明: by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine tsum_congr fun f => ENNReal.tsum_mul_left.symm.trans (tsum_congr fun a => ?_)
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (p a) 0

@[simp]

Depends on / 依赖: ENNReal, ENNReal.tsum_mul_left.symm.trans, bind_apply, mul_boole, mul_ite, mul_zero, pure_apply, tsum_congr, tsum_mul_left
-/
theorem seq_apply : (seq q p) b = ∑' (f : α -> β) (a : α), if b = f a then q f * p a else 0 := by
  simp only [seq, mul_boole, bind_apply, pure_apply]
  refine tsum_congr fun f => ENNReal.tsum_mul_left.symm.trans (tsum_congr fun a => ?_)
  simpa only [mul_zero] using mul_ite (b = f a) (q f) (p a) 0

@[simp]
/--
theorem `support_seq` / 定理 `support_seq`

English:
theorem support_seq
  statement: (seq q p).support = ⋃ f in q.support, f '' p.support
  proof: Set.ext fun b => by simp [-mem_support_iff, seq, @eq_comm β b]

中文:
定理 support_seq
  结论: (seq q p).support = ⋃ f in q.support, f '' p.support
  证明: Set.ext fun b => by simp [-mem_support_iff, seq, @eq_comm β b]

Depends on / 依赖: Set.ext, eq_comm, mem_support_iff
-/
theorem support_seq : (seq q p).support = ⋃ f in q.support, f '' p.support :=
  Set.ext fun b => by simp [-mem_support_iff, seq, @eq_comm β b]

/--
theorem `mem_support_seq_iff` / 定理 `mem_support_seq_iff`

English:
theorem mem_support_seq_iff
  statement: b in (seq q p).support ↔ exists f in q.support, b in f '' p.support
  proof: by simp

中文:
定理 mem_support_seq_iff
  结论: b in (seq q p).support ↔ 存在 f in q.support, b in f '' p.support
  证明: by simp
-/
theorem mem_support_seq_iff : b in (seq q p).support ↔ exists f in q.support, b in f '' p.support := by simp

end Seq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulFunctor PMF
  body: rfl
  id_map := bind_pure
  comp_map _ _ _ := (map_comp _ _ _).symm

中文:
实例 :
  签名: LawfulFunctor PMF
  定义体: rfl
  id_map := bind_pure
  comp_map _ _ _ := (map_comp _ _ _).symm
-/
instance : LawfulFunctor PMF where
  map_const := rfl
  id_map := bind_pure
  comp_map _ _ _ := (map_comp _ _ _).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad PMF
  body: LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)

中文:
实例 :
  签名: LawfulMonad PMF
  定义体: LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)

Depends on / 依赖: LawfulMonad, LawfulMonad.mk
-/
instance : LawfulMonad PMF := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => rfl)
  (id_map := id_map)
  (pure_bind := pure_bind)
  (bind_assoc := bind_bind)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ULiftable PMF.{u} PMF.{v}
  body: { toFun := map e, invFun := map e.symm
      left_inv := fun a => by simp [map_comp, map_id]
      right_inv := fun a => by simp [map_comp, map_id] }

中文:
实例 :
  签名: ULiftable PMF.{u} PMF.{v}
  定义体: { toFun := map e, invFun := map e.symm
      left_inv := fun a => by simp [map_comp, map_id]
      right_inv := fun a => by simp [map_comp, map_id] }

Depends on / 依赖: e.symm, invFun, left_inv, map_comp, map_id, right_inv
-/
instance : ULiftable PMF.{u} PMF.{v} where
  congr e :=
    { toFun := map e, invFun := map e.symm
      left_inv := fun a => by simp [map_comp, map_id]
      right_inv := fun a => by simp [map_comp, map_id] }

section OfFinset

/--
Definition of `ofFinset` / `ofFinset` 的定义

English:
definition ofFinset
  signature: (f : α -> Real>=0∞) (s : Finset α) (h : ∑ a in s, f a = 1)
  body: ⟨f, h ▸ hasSum_sum_of_ne_finset_zero h'⟩

中文:
定义 ofFinset
  签名: (f : α -> 实数>=0∞) (s : Finset α) (h : ∑ a in s, f a = 1)
  定义体: ⟨f, h ▸ hasSum_sum_of_ne_finset_zero h'⟩

Depends on / 依赖: hasSum_sum_of_ne_finset_zero
-/
def ofFinset (f : α -> Real>=0∞) (s : Finset α) (h : ∑ a in s, f a = 1)
    (h' : forall (a) (_ : a ∉ s), f a = 0) : PMF α :=
  ⟨f, h ▸ hasSum_sum_of_ne_finset_zero h'⟩

variable {f : α -> Real>=0∞} {s : Finset α} (h : ∑ a in s, f a = 1) (h' : forall (a) (_ : a ∉ s), f a = 0)

@[simp]
/--
theorem `ofFinset_apply` / 定理 `ofFinset_apply`

English:
theorem ofFinset_apply
  given: (a : α)
  statement: ofFinset f s h h' a = f a
  proof: rfl

@[simp]

中文:
定理 ofFinset_apply
  条件: (a : α)
  结论: ofFinset f s h h' a = f a
  证明: rfl

@[simp]
-/
theorem ofFinset_apply (a : α) : ofFinset f s h h' a = f a := rfl

@[simp]
/--
theorem `support_ofFinset` / 定理 `support_ofFinset`

English:
theorem support_ofFinset
  statement: (ofFinset f s h h').support = ↑s inter Function.support f
  proof: Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)

中文:
定理 support_ofFinset
  结论: (ofFinset f s h h').support = ↑s inter Function.support f
  证明: Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)

Depends on / 依赖: Set.ext, mem_support_iff
-/
theorem support_ofFinset : (ofFinset f s h h').support = ↑s inter Function.support f :=
  Set.ext fun a => by simpa [mem_support_iff] using mt (h' a)

/--
theorem `mem_support_ofFinset_iff` / 定理 `mem_support_ofFinset_iff`

English:
theorem mem_support_ofFinset_iff
  given: (a : α)
  statement: a in (ofFinset f s h h').support ↔ a in s ∧ f a != 0
  proof: by
  simp

中文:
定理 mem_support_ofFinset_iff
  条件: (a : α)
  结论: a in (ofFinset f s h h').support ↔ a in s ∧ f a != 0
  证明: by
  simp
-/
theorem mem_support_ofFinset_iff (a : α) : a in (ofFinset f s h h').support ↔ a in s ∧ f a != 0 := by
  simp

/--
theorem `ofFinset_apply_of_notMem` / 定理 `ofFinset_apply_of_notMem`

English:
theorem ofFinset_apply_of_notMem
  given: {a : α} (ha : a ∉ s)
  statement: ofFinset f s h h' a = 0
  proof: h' a ha

中文:
定理 ofFinset_apply_of_notMem
  条件: {a : α} (ha : a ∉ s)
  结论: ofFinset f s h h' a = 0
  证明: h' a ha
-/
theorem ofFinset_apply_of_notMem {a : α} (ha : a ∉ s) : ofFinset f s h h' a = 0 :=
  h' a ha

section Measure

variable (t : Set α)

@[simp]
/--
theorem `toOuterMeasure_ofFinset_apply` / 定理 `toOuterMeasure_ofFinset_apply`

English:
theorem toOuterMeasure_ofFinset_apply
  proof: toOuterMeasure_apply (ofFinset f s h h') t

@[simp]

中文:
定理 toOuterMeasure_ofFinset_apply
  证明: toOuterMeasure_apply (ofFinset f s h h') t

@[simp]

Depends on / 依赖: ofFinset, toOuterMeasure_apply
-/
theorem toOuterMeasure_ofFinset_apply :
    (ofFinset f s h h').toOuterMeasure t = ∑' x, t.indicator f x :=
  toOuterMeasure_apply (ofFinset f s h h') t

@[simp]
/--
theorem `toMeasure_ofFinset_apply` / 定理 `toMeasure_ofFinset_apply`

English:
theorem toMeasure_ofFinset_apply
  given: [MeasurableSpace α] (ht : MeasurableSet t)
  proof: (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_ofFinset_apply h h' t)

中文:
定理 toMeasure_ofFinset_apply
  条件: [MeasurableSpace α] (ht : MeasurableSet t)
  证明: (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_ofFinset_apply h h' t)

Depends on / 依赖: toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_ofFinset_apply
-/
theorem toMeasure_ofFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (ofFinset f s h h').toMeasure t = ∑' x, t.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_ofFinset_apply h h' t)

end Measure

end OfFinset

section OfFintype

/--
Definition of `ofFintype` / `ofFintype` 的定义

English:
definition ofFintype
  signature: [Fintype α] (f : α -> Real>=0∞) (h : ∑ a, f a = 1)
  body: ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

中文:
定义 ofFintype
  签名: [Fintype α] (f : α -> 实数>=0∞) (h : ∑ a, f a = 1)
  定义体: ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ, absurd, mem_univ, ofFinset
-/
def ofFintype [Fintype α] (f : α -> Real>=0∞) (h : ∑ a, f a = 1) : PMF α :=
  ofFinset f Finset.univ h fun a ha => absurd (Finset.mem_univ a) ha

variable [Fintype α] {f : α -> Real>=0∞} (h : ∑ a, f a = 1)

@[simp]
/--
theorem `ofFintype_apply` / 定理 `ofFintype_apply`

English:
theorem ofFintype_apply
  given: (a : α)
  statement: ofFintype f h a = f a
  proof: rfl

@[simp]

中文:
定理 ofFintype_apply
  条件: (a : α)
  结论: ofFintype f h a = f a
  证明: rfl

@[simp]
-/
theorem ofFintype_apply (a : α) : ofFintype f h a = f a := rfl

@[simp]
/--
theorem `support_ofFintype` / 定理 `support_ofFintype`

English:
theorem support_ofFintype
  statement: (ofFintype f h).support = Function.support f
  proof: rfl

中文:
定理 support_ofFintype
  结论: (ofFintype f h).support = Function.support f
  证明: rfl
-/
theorem support_ofFintype : (ofFintype f h).support = Function.support f := rfl

/--
theorem `mem_support_ofFintype_iff` / 定理 `mem_support_ofFintype_iff`

English:
theorem mem_support_ofFintype_iff
  given: (a : α)
  statement: a in (ofFintype f h).support ↔ f a != 0
  proof: Iff.rfl

中文:
定理 mem_support_ofFintype_iff
  条件: (a : α)
  结论: a in (ofFintype f h).support ↔ f a != 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_support_ofFintype_iff (a : α) : a in (ofFintype f h).support ↔ f a != 0 := Iff.rfl

open scoped Classical in
@[simp]
/--
lemma `map_ofFintype` / 引理 `map_ofFintype`

English:
lemma map_ofFintype
  given: [Fintype β] (f : α -> Real>=0∞) (h : ∑ a, f a = 1) (g : α -> β)
  proof: by
  ext b : 1
  simp only [sum_filter, eq_comm, map_apply, ofFintype_apply]
  exact tsum_eq_sum fun _ h => (h <| mem_univ _).elim

中文:
引理 map_ofFintype
  条件: [Fintype β] (f : α -> 实数>=0∞) (h : ∑ a, f a = 1) (g : α -> β)
  证明: by
  ext b : 1
  simp only [sum_filter, eq_comm, map_apply, ofFintype_apply]
  exact tsum_eq_sum fun _ h => (h <| mem_univ _).elim

Depends on / 依赖: eq_comm, map_apply, mem_univ, ofFintype_apply, sum_filter, tsum_eq_sum
-/
lemma map_ofFintype [Fintype β] (f : α -> Real>=0∞) (h : ∑ a, f a = 1) (g : α -> β) :
    (ofFintype f h).map g = ofFintype (fun b => ∑ a with g a = b, f a)
      (by simpa [Finset.sum_fiberwise_eq_sum_filter univ univ g f]) := by
  ext b : 1
  simp only [sum_filter, eq_comm, map_apply, ofFintype_apply]
  exact tsum_eq_sum fun _ h => (h <| mem_univ _).elim

section Measure

variable (s : Set α)

@[simp high]
/--
theorem `toOuterMeasure_ofFintype_apply` / 定理 `toOuterMeasure_ofFintype_apply`

English:
theorem toOuterMeasure_ofFintype_apply
  statement: (ofFintype f h).toOuterMeasure s = ∑' x, s.indicator f x
  proof: toOuterMeasure_apply (ofFintype f h) s

@[simp]

中文:
定理 toOuterMeasure_ofFintype_apply
  结论: (ofFintype f h).toOuterMeasure s = ∑' x, s.indicator f x
  证明: toOuterMeasure_apply (ofFintype f h) s

@[simp]

Depends on / 依赖: ofFintype, toOuterMeasure_apply
-/
theorem toOuterMeasure_ofFintype_apply : (ofFintype f h).toOuterMeasure s = ∑' x, s.indicator f x :=
  toOuterMeasure_apply (ofFintype f h) s

@[simp]
/--
theorem `toMeasure_ofFintype_apply` / 定理 `toMeasure_ofFintype_apply`

English:
theorem toMeasure_ofFintype_apply
  given: [MeasurableSpace α] (hs : MeasurableSet s)
  proof: (toMeasure_apply_eq_toOuterMeasure_apply _ hs).trans (toOuterMeasure_ofFintype_apply h s)

中文:
定理 toMeasure_ofFintype_apply
  条件: [MeasurableSpace α] (hs : MeasurableSet s)
  证明: (toMeasure_apply_eq_toOuterMeasure_apply _ hs).trans (toOuterMeasure_ofFintype_apply h s)

Depends on / 依赖: toMeasure_apply_eq_toOuterMeasure_apply, toOuterMeasure_ofFintype_apply
-/
theorem toMeasure_ofFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) :
    (ofFintype f h).toMeasure s = ∑' x, s.indicator f x :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ hs).trans (toOuterMeasure_ofFintype_apply h s)

end Measure

end OfFintype

section normalize

/--
Definition of `normalize` / `normalize` 的定义

English:
definition normalize
  signature: (f : α -> Real>=0∞) (hf0 : tsum f != 0) (hf : tsum f != ∞)
  body: ⟨fun a => f a * (∑' x, f x)⁻¹,
    ENNReal.summable.hasSum_iff.2 (ENNReal.tsum_mul_right.trans (ENNReal.mul_inv_cancel hf0 hf))⟩

中文:
定义 normalize
  签名: (f : α -> 实数>=0∞) (hf0 : tsum f != 0) (hf : tsum f != ∞)
  定义体: ⟨fun a => f a * (∑' x, f x)⁻¹,
    ENNReal.summable.hasSum_iff.2 (ENNReal.tsum_mul_right.trans (ENNReal.mul_inv_cancel hf0 hf))⟩

Depends on / 依赖: ENNReal, ENNReal.mul_inv_cancel, ENNReal.summable.hasSum_iff, ENNReal.tsum_mul_right.trans, hasSum_iff, mul_inv_cancel, summable, tsum_mul_right
-/
def normalize (f : α -> Real>=0∞) (hf0 : tsum f != 0) (hf : tsum f != ∞) : PMF α :=
  ⟨fun a => f a * (∑' x, f x)⁻¹,
    ENNReal.summable.hasSum_iff.2 (ENNReal.tsum_mul_right.trans (ENNReal.mul_inv_cancel hf0 hf))⟩

variable {f : α -> Real>=0∞} (hf0 : tsum f != 0) (hf : tsum f != ∞)

@[simp]
/--
theorem `normalize_apply` / 定理 `normalize_apply`

English:
theorem normalize_apply
  given: (a : α)
  statement: (normalize f hf0 hf) a = f a * (∑' x, f x)⁻¹
  proof: rfl

@[simp]

中文:
定理 normalize_apply
  条件: (a : α)
  结论: (normalize f hf0 hf) a = f a * (∑' x, f x)⁻¹
  证明: rfl

@[simp]
-/
theorem normalize_apply (a : α) : (normalize f hf0 hf) a = f a * (∑' x, f x)⁻¹ := rfl

@[simp]
/--
theorem `support_normalize` / 定理 `support_normalize`

English:
theorem support_normalize
  statement: (normalize f hf0 hf).support = Function.support f
  proof: Set.ext fun a => by simp [hf, mem_support_iff]

中文:
定理 support_normalize
  结论: (normalize f hf0 hf).support = Function.support f
  证明: Set.ext fun a => by simp [hf, mem_support_iff]

Depends on / 依赖: Set.ext, isClosedEmbedding_subtypeVal, isClosedEmbedding_subtypeVal.quasiSober, isClosed_zeroLocus, mem_support_iff, quasiSober
-/
theorem support_normalize : (normalize f hf0 hf).support = Function.support f :=
  Set.ext fun a => by simp [hf, mem_support_iff]

/--
theorem `mem_support_normalize_iff` / 定理 `mem_support_normalize_iff`

English:
theorem mem_support_normalize_iff
  given: (a : α)
  statement: a in (normalize f hf0 hf).support ↔ f a != 0
  proof: by simp

中文:
定理 mem_support_normalize_iff
  条件: (a : α)
  结论: a in (normalize f hf0 hf).support ↔ f a != 0
  证明: by simp
-/
theorem mem_support_normalize_iff (a : α) : a in (normalize f hf0 hf).support ↔ f a != 0 := by simp

end normalize

section Filter

/--
Definition of `filter` / `filter` 的定义

English:
definition filter
  signature: (p : PMF α) (s : Set α) (h : exists a in s, a in p.support)
  body: PMF.normalize (s.indicator p) (by simpa using h) (p.tsum_coe_indicator_ne_top s)

中文:
定义 filter
  签名: (p : PMF α) (s : Set α) (h : 存在 a in s, a in p.support)
  定义体: PMF.normalize (s.indicator p) (by simpa using h) (p.tsum_coe_indicator_ne_top s)

Depends on / 依赖: PMF.normalize, indicator, normalize, p.tsum_coe_indicator_ne_top, s.indicator, tsum_coe_indicator_ne_top
-/
def filter (p : PMF α) (s : Set α) (h : exists a in s, a in p.support) : PMF α :=
  PMF.normalize (s.indicator p) (by simpa using h) (p.tsum_coe_indicator_ne_top s)

variable {p : PMF α} {s : Set α} (h : exists a in s, a in p.support)

@[simp]
/--
theorem `filter_apply` / 定理 `filter_apply`

English:
theorem filter_apply
  given: (a : α)
  proof: by
  rw [filter]; rw [normalize_apply]

中文:
定理 filter_apply
  条件: (a : α)
  证明: by
  rw [filter]; rw [normalize_apply]

Depends on / 依赖: filter, normalize_apply
-/
theorem filter_apply (a : α) :
    (p.filter s h) a = s.indicator p a * (∑' a', (s.indicator p) a')⁻¹ := by
  rw [filter]; rw [normalize_apply]

/--
theorem `filter_apply_eq_zero_of_notMem` / 定理 `filter_apply_eq_zero_of_notMem`

English:
theorem filter_apply_eq_zero_of_notMem
  given: {a : α} (ha : a ∉ s)
  statement: (p.filter s h) a = 0
  proof: by
  rw [filter_apply]; rw [Set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha]; rw [zero_mul]

中文:
定理 filter_apply_eq_zero_of_notMem
  条件: {a : α} (ha : a ∉ s)
  结论: (p.filter s h) a = 0
  证明: by
  rw [filter_apply]; rw [Set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha]; rw [zero_mul]

Depends on / 依赖: Set.indicator_apply_eq_zero.mpr, absurd, filter_apply, indicator_apply_eq_zero, zero_mul
-/
theorem filter_apply_eq_zero_of_notMem {a : α} (ha : a ∉ s) : (p.filter s h) a = 0 := by
  rw [filter_apply]; rw [Set.indicator_apply_eq_zero.mpr fun ha' => absurd ha' ha]; rw [zero_mul]

/--
theorem `mem_support_filter_iff` / 定理 `mem_support_filter_iff`

English:
theorem mem_support_filter_iff
  given: {a : α}
  statement: a in (p.filter s h).support ↔ a in s ∧ a in p.support
  proof: (mem_support_normalize_iff _ _ _).trans Set.indicator_apply_ne_zero

@[simp]

中文:
定理 mem_support_filter_iff
  条件: {a : α}
  结论: a in (p.filter s h).support ↔ a in s ∧ a in p.support
  证明: (mem_support_normalize_iff _ _ _).trans Set.indicator_apply_ne_zero

@[simp]

Depends on / 依赖: Set.indicator_apply_ne_zero, indicator_apply_ne_zero, mem_support_normalize_iff
-/
theorem mem_support_filter_iff {a : α} : a in (p.filter s h).support ↔ a in s ∧ a in p.support :=
  (mem_support_normalize_iff _ _ _).trans Set.indicator_apply_ne_zero

@[simp]
/--
theorem `support_filter` / 定理 `support_filter`

English:
theorem support_filter
  statement: (p.filter s h).support = s inter p.support
  proof: Set.ext fun _ => mem_support_filter_iff _

中文:
定理 support_filter
  结论: (p.filter s h).support = s inter p.support
  证明: Set.ext fun _ => mem_support_filter_iff _

Depends on / 依赖: Set.ext, mem_support_filter_iff
-/
theorem support_filter : (p.filter s h).support = s inter p.support :=
  Set.ext fun _ => mem_support_filter_iff _

/--
theorem `filter_apply_eq_zero_iff` / 定理 `filter_apply_eq_zero_iff`

English:
theorem filter_apply_eq_zero_iff
  given: (a : α)
  statement: (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support
  proof: by
  rw [apply_eq_zero_iff]; rw [support_filter]; rw [Set.mem_inter_iff]; rw [not_and_or]

中文:
定理 filter_apply_eq_zero_iff
  条件: (a : α)
  结论: (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support
  证明: by
  rw [apply_eq_zero_iff]; rw [support_filter]; rw [Set.mem_inter_iff]; rw [not_and_or]

Depends on / 依赖: Set.mem_inter_iff, apply_eq_zero_iff, mem_inter_iff, not_and_or, support_filter
-/
theorem filter_apply_eq_zero_iff (a : α) : (p.filter s h) a = 0 ↔ a ∉ s ∨ a ∉ p.support := by
  rw [apply_eq_zero_iff]; rw [support_filter]; rw [Set.mem_inter_iff]; rw [not_and_or]

/--
theorem `filter_apply_ne_zero_iff` / 定理 `filter_apply_ne_zero_iff`

English:
theorem filter_apply_ne_zero_iff
  given: (a : α)
  statement: (p.filter s h) a != 0 ↔ a in s ∧ a in p.support
  proof: by
  rw [Ne]; rw [filter_apply_eq_zero_iff]; rw [not_or]; rw [Classical.not_not]; rw [Classical.not_not]

中文:
定理 filter_apply_ne_zero_iff
  条件: (a : α)
  结论: (p.filter s h) a != 0 ↔ a in s ∧ a in p.support
  证明: by
  rw [Ne]; rw [filter_apply_eq_zero_iff]; rw [not_or]; rw [Classical.not_not]; rw [Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, filter_apply_eq_zero_iff, not_not, not_or
-/
theorem filter_apply_ne_zero_iff (a : α) : (p.filter s h) a != 0 ↔ a in s ∧ a in p.support := by
  rw [Ne]; rw [filter_apply_eq_zero_iff]; rw [not_or]; rw [Classical.not_not]; rw [Classical.not_not]

end Filter

section bernoulli

/-- A `PMF` which assigns probability `p` to `true` and `1 - p` to `false`. -/
@[deprecated ProbabilityTheory.bernoulliMeasure (since := "2026-04-07")]
/--
Definition of `bernoulli` / `bernoulli` 的定义

English:
definition bernoulli
  signature: (p : Real>=0) (h : p <= 1)
  body: ofFintype (fun b => cond b p (1 - p)) (by simp [h])

中文:
定义 bernoulli
  签名: (p : 实数>=0) (h : p <= 1)
  定义体: ofFintype (fun b => cond b p (1 - p)) (by simp [h])

Depends on / 依赖: ofFintype
-/
def bernoulli (p : Real>=0) (h : p <= 1) : PMF Bool :=
  ofFintype (fun b => cond b p (1 - p)) (by simp [h])

variable {p : Real>=0} (h : p <= 1) (b : Bool)

@[deprecated ProbabilityTheory.bernoulliMeasure_apply (since := "2026-04-07")]
/--
theorem `bernoulli_apply` / 定理 `bernoulli_apply`

English:
theorem bernoulli_apply
  statement: bernoulli p h b = cond b p (1 - p)
  proof: by
  simp only [bernoulli, ofFintype_apply]
  exact Eq.symm (Bool.apply_cond ofNNReal)

@[deprecated ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_notMem (since := "2026-05-29")]

中文:
定理 bernoulli_apply
  结论: bernoulli p h b = cond b p (1 - p)
  证明: by
  simp only [bernoulli, ofFintype_apply]
  exact Eq.symm (Bool.apply_cond ofNNReal)

@[deprecated ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_notMem (since := "2026-05-29")]

Depends on / 依赖: Bool.apply_cond, Eq.symm, apply_cond, bernoulli, ofFintype_apply, ofNNReal
-/
theorem bernoulli_apply : bernoulli p h b = cond b p (1 - p) := by
  simp only [bernoulli, ofFintype_apply]
  exact Eq.symm (Bool.apply_cond ofNNReal)

@[deprecated ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_notMem (since := "2026-05-29")]
/--
theorem `support_bernoulli` / 定理 `support_bernoulli`

English:
theorem support_bernoulli
  statement: (bernoulli p h).support = { b | cond b (p != 0) (p != 1) }
  proof: by
  refine Set.ext fun b => ?_
  induction b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne, ENNReal.coe_sub,
      ENNReal.coe_one, Bool.cond_prop, Set.mem_ofPred_eq, Bool.false_eq_true, ite_false,
      not_iff_not]
    constructor
    · intro h'
      simp only [tsub_eq_zero_

中文:
定理 support_bernoulli
  结论: (bernoulli p h).support = { b | cond b (p != 0) (p != 1) }
  证明: by
  refine Set.ext fun b => ?_
  induction b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne, ENNReal.coe_sub,
      ENNReal.coe_one, Bool.cond_prop, Set.mem_ofPred_eq, Bool.false_eq_true, ite_false,
      not_iff_not]
    constructor
    · intro h'
      simp only [tsub_eq_zero_

Depends on / 依赖: Bool.cond_false, Bool.cond_prop, Bool.cond_true, Bool.false_eq_true, ENNReal, ENNReal.coe_eq_zero, ENNReal.coe_one, ENNReal.coe_sub, Set.ext, Set.mem_ofPred_eq, bernoulli_apply, coe_eq_zero, coe_one, coe_sub, cond_false, cond_prop, cond_true, eq_of_le_of_ge, false_eq_true, ite_false
-/
theorem support_bernoulli : (bernoulli p h).support = { b | cond b (p != 0) (p != 1) } := by
  refine Set.ext fun b => ?_
  induction b
  · simp_rw [mem_support_iff, bernoulli_apply, Bool.cond_false, Ne, ENNReal.coe_sub,
      ENNReal.coe_one, Bool.cond_prop, Set.mem_ofPred_eq, Bool.false_eq_true, ite_false,
      not_iff_not]
    constructor
    · intro h'
      simp only [tsub_eq_zero_iff_le, one_le_coe_iff] at h'
      exact eq_of_le_of_ge h h'
    · intro h'
      simp only [h', ENNReal.coe_one, tsub_self]
  · simp only [mem_support_iff, bernoulli_apply, Bool.cond_true, Set.mem_ofPred_eq, ne_eq,
      ENNReal.coe_eq_zero]

@[deprecated ProbabilityTheory.bernoulliMeasure_apply_of_notMem_of_notMem (since := "2026-05-29")]
/--
theorem `mem_support_bernoulli_iff` / 定理 `mem_support_bernoulli_iff`

English:
theorem mem_support_bernoulli_iff
  statement: b in (bernoulli p h).support ↔ cond b (p != 0) (p != 1)
  proof: by
  simp [support_bernoulli]

中文:
定理 mem_support_bernoulli_iff
  结论: b in (bernoulli p h).support ↔ cond b (p != 0) (p != 1)
  证明: by
  simp [support_bernoulli]

Depends on / 依赖: support_bernoulli
-/
theorem mem_support_bernoulli_iff : b in (bernoulli p h).support ↔ cond b (p != 0) (p != 1) := by
  simp [support_bernoulli]

end bernoulli

end

end PMF
