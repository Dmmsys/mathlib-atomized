/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Order.LeftRightLim

/-!
# Stieltjes measures on the real line

Consider a function `f : ℝ → ℝ` which is monotone and right-continuous. Then one can define a
corresponding measure, giving mass `f b - f a` to the interval `(a, b]`. We implement more
generally this notion for `f : R → ℝ` where `R` is a conditionally complete dense linear order.

## Main definitions

* `StieltjesFunction R` is a structure containing a function from `R → ℝ`, together with the
  assertions that it is monotone and right-continuous. To `f : StieltjesFunction R`, one associates
  a Borel measure `f.measure`.
* `f.measure_Ioc` asserts that `f.measure (Ioc a b) = ofReal (f b - f a)`
* `f.measure_Ioo` asserts that `f.measure (Ioo a b) = ofReal (leftLim f b - f a)`.
* `f.measure_Icc` and `f.measure_Ico` are analogous.
* `Monotone.stieltjesFunction`: to a monotone function `f`, associate the Stieltjes function
  equal to the right limit of `f`. This makes it possible to associate a Stieltjes measure to
  any monotone function.

## Implementation

We define Stieltjes functions over any conditionally complete dense linear order, to be able
to cover the cases of `ℝ≥0` and `[0, T]` in addition to the classical case of `ℝ`. This creates
a few issues, mostly with the management of bottom and top elements. To handle these, we need
two technical definitions:
* `Iotop a b` is the interval `Ioo a b` if `b` is not top, and `Ioc a b` if `b` is top.
* `botSet` is the empty set if there is no bot element, and `{x}` if `x` is bot.

Note that the theory of Stieltjes measures is not completely satisfactory when there is a bot
element `x`: any Stieltjes measure gives zero mass to `{x}` in this case, so the Dirac mass at `x`
is not representable as a Stieltjes measure.
-/

@[expose] public section

noncomputable section

open Set Filter Function ENNReal NNReal Topology MeasureTheory

open ENNReal (ofReal)

section Prerequisites

variable {R : Type*} [LinearOrder R]

open scoped Classical in
/--
Definition of `Iotop` / `Iotop` 的定义

English:
definition Iotop
  signature: (a b : R)
  body: if IsTop b then Ioc a b else Ioo a b

中文:
定义 Iotop
  签名: (a b : R)
  定义体: if IsTop b then Ioc a b else Ioo a b
-/
def Iotop (a b : R) : Set R := if IsTop b then Ioc a b else Ioo a b

/--
lemma `Iotop_subset_Ioc` / 引理 `Iotop_subset_Ioc`

English:
lemma Iotop_subset_Ioc
  given: {a b : R}
  statement: Iotop a b subseteq Ioc a b
  proof: by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]

中文:
引理 Iotop_subset_Ioc
  条件: {a b : R}
  结论: Iotop a b subseteq Ioc a b
  证明: by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]

Depends on / 依赖: Ioo_subset_Ioc_self, split_ifs
-/
lemma Iotop_subset_Ioc {a b : R} : Iotop a b subseteq Ioc a b := by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]

/--
lemma `Ioo_subset_Iotop` / 引理 `Ioo_subset_Iotop`

English:
lemma Ioo_subset_Iotop
  given: {a b : R}
  statement: Ioo a b subseteq Iotop a b
  proof: by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]

中文:
引理 Ioo_subset_Iotop
  条件: {a b : R}
  结论: Ioo a b subseteq Iotop a b
  证明: by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]

Depends on / 依赖: Ioo_subset_Ioc_self, split_ifs
-/
lemma Ioo_subset_Iotop {a b : R} : Ioo a b subseteq Iotop a b := by
  simp only [Iotop]
  split_ifs with h <;> simp [Ioo_subset_Ioc_self]

/--
lemma `isOpen_Iotop` / 引理 `isOpen_Iotop`

English:
lemma isOpen_Iotop
  given: [TopologicalSpace R] [OrderTopology R] (a b : R)
  statement: IsOpen (Iotop a b)
  proof: by
  simp only [Iotop]
  split_ifs with h
  · have : Ioc a b = Ioi a := Subset.antisymm (fun x hx => hx.1) (fun x hx => by exact ⟨hx, h _⟩)
    simp [this, isOpen_Ioi]
  · simp [isOpen_Ioo]

中文:
引理 isOpen_Iotop
  条件: [TopologicalSpace R] [OrderTopology R] (a b : R)
  结论: IsOpen (Iotop a b)
  证明: by
  simp only [Iotop]
  split_ifs with h
  · have : Ioc a b = Ioi a := Subset.antisymm (fun x hx => hx.1) (fun x hx => by exact ⟨hx, h _⟩)
    simp [this, isOpen_Ioi]
  · simp [isOpen_Ioo]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, isOpen_Ioi, isOpen_Ioo, split_ifs
-/
lemma isOpen_Iotop [TopologicalSpace R] [OrderTopology R] (a b : R) : IsOpen (Iotop a b) := by
  simp only [Iotop]
  split_ifs with h
  · have : Ioc a b = Ioi a := Subset.antisymm (fun x hx => hx.1) (fun x hx => by exact ⟨hx, h _⟩)
    simp [this, isOpen_Ioi]
  · simp [isOpen_Ioo]

/--
Definition of `botSet` / `botSet` 的定义

English:
definition botSet
  signature: : Set R
  body: {x | IsBot x}

中文:
定义 botSet
  签名: : Set R
  定义体: {x | IsBot x}
-/
def botSet : Set R := {x | IsBot x}

/--
lemma `Ioc_sdiff_botSet` / 引理 `Ioc_sdiff_botSet`

English:
lemma Ioc_sdiff_botSet
  given: (a b : R)
  statement: Ioc a b \ botSet = Ioc a b
  proof: by
  rw [sdiff_eq_left]; rw [disjoint_iff_forall_ne]
  rintro c ⟨hc, _⟩ _ hc' rfl
  exact (hc' a).not_gt hc

@[deprecated (since := "2026-06-03")] alias Ioc_diff_botSet := Ioc_sdiff_botSet

中文:
引理 Ioc_sdiff_botSet
  条件: (a b : R)
  结论: Ioc a b \ botSet = Ioc a b
  证明: by
  rw [sdiff_eq_left]; rw [disjoint_iff_forall_ne]
  rintro c ⟨hc, _⟩ _ hc' rfl
  exact (hc' a).not_gt hc

@[deprecated (since := "2026-06-03")] alias Ioc_diff_botSet := Ioc_sdiff_botSet
-/
@[simp] lemma Ioc_sdiff_botSet (a b : R) : Ioc a b \ botSet = Ioc a b := by
  rw [sdiff_eq_left]; rw [disjoint_iff_forall_ne]
  rintro c ⟨hc, _⟩ _ hc' rfl
  exact (hc' a).not_gt hc

@[deprecated (since := "2026-06-03")] alias Ioc_diff_botSet := Ioc_sdiff_botSet

/--
lemma `notMem_botSet_of_lt` / 引理 `notMem_botSet_of_lt`

English:
lemma notMem_botSet_of_lt
  given: {x y : R} (h : x < y)
  statement: y ∉ botSet
  proof: by
  contrapose! h
  exact h x

中文:
引理 notMem_botSet_of_lt
  条件: {x y : R} (h : x < y)
  结论: y ∉ botSet
  证明: by
  contrapose! h
  exact h x

Depends on / 依赖: contrapose
-/
lemma notMem_botSet_of_lt {x y : R} (h : x < y) : y ∉ botSet := by
  contrapose! h
  exact h x

/--
lemma `subsingleton_botSet` / 引理 `subsingleton_botSet`

English:
lemma subsingleton_botSet
  statement: (botSet (R := R)).Subsingleton
  proof: subsingleton_isBot _

中文:
引理 subsingleton_botSet
  结论: (botSet (R := R)).Subsingleton
  证明: subsingleton_isBot _

Depends on / 依赖: Subsingleton
-/
lemma subsingleton_botSet : (botSet (R := R)).Subsingleton :=
  subsingleton_isBot _

/--
lemma `measurableSet_botSet` / 引理 `measurableSet_botSet`

English:
lemma measurableSet_botSet
  given: [MeasurableSpace R] [MeasurableSingletonClass R]
  proof: subsingleton_botSet.measurableSet

中文:
引理 measurableSet_botSet
  条件: [MeasurableSpace R] [MeasurableSingletonClass R]
  证明: subsingleton_botSet.measurableSet
-/
lemma measurableSet_botSet [MeasurableSpace R] [MeasurableSingletonClass R] :
    MeasurableSet (botSet (R := R)) :=
  subsingleton_botSet.measurableSet

/--
lemma `botSet_eq_singleton_of_isBot` / 引理 `botSet_eq_singleton_of_isBot`

English:
lemma botSet_eq_singleton_of_isBot
  given: {x : R} (hx : IsBot x)
  statement: botSet = {x}
  proof: (subsingleton_botSet (R := R)).eq_singleton_of_mem hx

中文:
引理 botSet_eq_singleton_of_isBot
  条件: {x : R} (hx : IsBot x)
  结论: botSet = {x}
  证明: (subsingleton_botSet (R := R)).eq_singleton_of_mem hx

Depends on / 依赖: eq_singleton_of_mem, subsingleton_botSet
-/
lemma botSet_eq_singleton_of_isBot {x : R} (hx : IsBot x) : botSet = {x} :=
  (subsingleton_botSet (R := R)).eq_singleton_of_mem hx

end Prerequisites

variable (R : Type*) [LinearOrder R] [TopologicalSpace R]

/-! ### Basic properties of Stieltjes functions -/

/--
Definition of `StieltjesFunction` / `StieltjesFunction` 的定义

English:
structure StieltjesFunction
  parameters: where
  axioms and operations (3):
    - toFun : R -> Real
    - mono' : Monotone toFun
    - right_continuous' : forall x, ContinuousWithinAt toFun (Ici x) x

中文:
结构 StieltjesFunction
  参数: where
  公理与运算 (3 个):
    - toFun : R -> 实数
    - mono' : Monotone toFun
    - right_continuous' : 对任意 x, ContinuousWithinAt toFun (Ici x) x
-/
structure StieltjesFunction where
  /-- The underlying function `R → ℝ`.

  Do NOT use directly. Use the coercion instead. -/
  toFun : R -> Real
  mono' : Monotone toFun
  right_continuous' : forall x, ContinuousWithinAt toFun (Ici x) x

namespace StieltjesFunction

variable {R}

attribute [coe] toFun

/--
Instance `instCoeFun` / 实例 `instCoeFun`

English:
instance instCoeFun
  signature: : CoeFun (StieltjesFunction R) fun _ => R -> Real
  body: ⟨toFun⟩

initialize_simps_projections StieltjesFunction (toFun -> apply)

中文:
实例 instCoeFun
  签名: : CoeFun (StieltjesFunction R) fun _ => R -> 实数
  定义体: ⟨toFun⟩

initialize_simps_projections StieltjesFunction (toFun -> apply)
-/
instance instCoeFun : CoeFun (StieltjesFunction R) fun _ => R -> Real :=
  ⟨toFun⟩

initialize_simps_projections StieltjesFunction (toFun -> apply)

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {f g : StieltjesFunction R} (h : forall x, f x = g x)
  statement: f = g
  proof: by
  exact (StieltjesFunction.mk.injEq ..).mpr (funext h)

中文:
引理 ext
  条件: {f g : StieltjesFunction R} (h : 对任意 x, f x = g x)
  结论: f = g
  证明: by
  exact (StieltjesFunction.mk.injEq ..).mpr (funext h)
-/
@[ext] lemma ext {f g : StieltjesFunction R} (h : forall x, f x = g x) : f = g := by
  exact (StieltjesFunction.mk.injEq ..).mpr (funext h)

variable (f : StieltjesFunction R)

@[gcongr]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  statement: Monotone f
  proof: f.mono'

中文:
定理 mono
  结论: Monotone f
  证明: f.mono'

Depends on / 依赖: f.mono
-/
theorem mono : Monotone f :=
  f.mono'

/--
theorem `right_continuous` / 定理 `right_continuous`

English:
theorem right_continuous
  given: (x : R)
  statement: ContinuousWithinAt f (Ici x) x
  proof: f.right_continuous' x

中文:
定理 right_continuous
  条件: (x : R)
  结论: ContinuousWithinAt f (Ici x) x
  证明: f.right_continuous' x

Depends on / 依赖: f.right_continuous, right_continuous
-/
theorem right_continuous (x : R) : ContinuousWithinAt f (Ici x) x :=
  f.right_continuous' x

/--
theorem `rightLim_eq` / 定理 `rightLim_eq`

English:
theorem rightLim_eq
  statement: [OrderTopology R]
  proof: by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq]; rw [continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x

中文:
定理 rightLim_eq
  结论: [OrderTopology R]
  证明: by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq]; rw [continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x

Depends on / 依赖: continuousWithinAt_Ioi_iff_Ici, continuousWithinAt_Ioi_iff_rightLim_eq, f.mono.continuousWithinAt_Ioi_iff_rightLim_eq, f.right_continuous, right_continuous
-/
theorem rightLim_eq [OrderTopology R]
    (f : StieltjesFunction R) (x : R) : Function.rightLim f x = f x := by
  rw [← f.mono.continuousWithinAt_Ioi_iff_rightLim_eq]; rw [continuousWithinAt_Ioi_iff_Ici]
  exact f.right_continuous' x

/--
theorem `iInf_Ioi_eq` / 定理 `iInf_Ioi_eq`

English:
theorem iInf_Ioi_eq
  statement: [OrderTopology R] [DenselyOrdered R] [NoMaxOrder R]
  proof: by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [f.mono.rightLim_eq_sInf]; rw [sInf_image']

中文:
定理 iInf_Ioi_eq
  结论: [OrderTopology R] [DenselyOrdered R] [NoMaxOrder R]
  证明: by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [f.mono.rightLim_eq_sInf]; rw [sInf_image']

Depends on / 依赖: Function, Function.rightLim, f.mono.rightLim_eq_sInf, f.rightLim_eq, rightLim, rightLim_eq, rightLim_eq_sInf, sInf_image
-/
theorem iInf_Ioi_eq [OrderTopology R] [DenselyOrdered R] [NoMaxOrder R]
     (f : StieltjesFunction R) (x : R) : ⨅ r : Ioi x, f r = f x := by
  suffices Function.rightLim f x = ⨅ r : Ioi x, f r by rw [← this, f.rightLim_eq]
  rw [f.mono.rightLim_eq_sInf]; rw [sInf_image']

/--
theorem `iInf_rat_gt_eq` / 定理 `iInf_rat_gt_eq`

English:
theorem iInf_rat_gt_eq
  given: (f : StieltjesFunction Real) (x : Real)
  proof: by
  rw [← iInf_Ioi_eq f x]
  refine (Real.iInf_Ioi_eq_iInf_rat_gt _ ?_ f.mono).symm
  refine ⟨f x, fun y => ?_⟩
  rintro ⟨y, hy_mem, rfl⟩
  exact f.mono (le_of_lt hy_mem)

中文:
定理 iInf_rat_gt_eq
  条件: (f : StieltjesFunction 实数) (x : 实数)
  证明: by
  rw [← iInf_Ioi_eq f x]
  refine (Real.iInf_Ioi_eq_iInf_rat_gt _ ?_ f.mono).symm
  refine ⟨f x, fun y => ?_⟩
  rintro ⟨y, hy_mem, rfl⟩
  exact f.mono (le_of_lt hy_mem)

Depends on / 依赖: Real.iInf_Ioi_eq_iInf_rat_gt, f.mono, hy_mem, iInf_Ioi_eq, iInf_Ioi_eq_iInf_rat_gt, le_of_lt
-/
theorem iInf_rat_gt_eq (f : StieltjesFunction Real) (x : Real) :
    ⨅ r : { r' : Rat // x < r' }, f r = f x := by
  rw [← iInf_Ioi_eq f x]
  refine (Real.iInf_Ioi_eq_iInf_rat_gt _ ?_ f.mono).symm
  refine ⟨f x, fun y => ?_⟩
  rintro ⟨y, hy_mem, rfl⟩
  exact f.mono (le_of_lt hy_mem)

/-- The identity of `ℝ` as a Stieltjes function, used to construct Lebesgue measure. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : StieltjesFunction Real where
  body: id
  mono' _ _ := id
  right_continuous' _ := continuousWithinAt_id

@[simp]

中文:
定义 id
  签名: : StieltjesFunction 实数 where
  定义体: id
  mono' _ _ := id
  right_continuous' _ := continuousWithinAt_id

@[simp]
-/
protected def id : StieltjesFunction Real where
  toFun := id
  mono' _ _ := id
  right_continuous' _ := continuousWithinAt_id

@[simp]
/--
theorem `id_leftLim` / 定理 `id_leftLim`

English:
theorem id_leftLim
  given: (x : Real)
  statement: leftLim StieltjesFunction.id x = x
  proof: continuousWithinAt_id.leftLim_eq

中文:
定理 id_leftLim
  条件: (x : 实数)
  结论: leftLim StieltjesFunction.id x = x
  证明: continuousWithinAt_id.leftLim_eq

Depends on / 依赖: continuousWithinAt_id, continuousWithinAt_id.leftLim_eq, leftLim_eq
-/
theorem id_leftLim (x : Real) : leftLim StieltjesFunction.id x = x :=
  continuousWithinAt_id.leftLim_eq

variable (R) in
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (c : Real)
  body: fun _ => c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const

中文:
定义 const
  签名: (c : 实数)
  定义体: fun _ => c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const
-/
protected def const (c : Real) : StieltjesFunction R where
  toFun := fun _ => c
  mono' _ _ := by simp
  right_continuous' _ := continuousWithinAt_const

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (StieltjesFunction R)
  body: ⟨StieltjesFunction.const R 0⟩

中文:
实例 instInhabited
  签名: : Inhabited (StieltjesFunction R)
  定义体: ⟨StieltjesFunction.const R 0⟩

Depends on / 依赖: StieltjesFunction, StieltjesFunction.const
-/
instance instInhabited : Inhabited (StieltjesFunction R) :=
  ⟨StieltjesFunction.const R 0⟩

/--
lemma `const_apply` / 引理 `const_apply`

English:
lemma const_apply
  given: (c : Real) (x : R)
  statement: (StieltjesFunction.const R c) x = c
  proof: rfl

中文:
引理 const_apply
  条件: (c : 实数) (x : R)
  结论: (StieltjesFunction.const R c) x = c
  证明: rfl
-/
@[simp] lemma const_apply (c : Real) (x : R) : (StieltjesFunction.const R c) x = c := rfl

/--
Definition of `add` / `add` 的定义

English:
definition add
  signature: (f g : StieltjesFunction R)
  body: fun x => f x + g x
  mono' := f.mono.add g.mono
  right_continuous' := fun x => (f.right_continuous x).add (g.right_continuous x)

中文:
定义 add
  签名: (f g : StieltjesFunction R)
  定义体: fun x => f x + g x
  mono' := f.mono.add g.mono
  right_continuous' := fun x => (f.right_continuous x).add (g.right_continuous x)
-/
protected def add (f g : StieltjesFunction R) : StieltjesFunction R where
  toFun := fun x => f x + g x
  mono' := f.mono.add g.mono
  right_continuous' := fun x => (f.right_continuous x).add (g.right_continuous x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddZeroClass (StieltjesFunction R)
  body: StieltjesFunction.add
  zero := StieltjesFunction.const R 0
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _

中文:
实例 :
  签名: AddZeroClass (StieltjesFunction R)
  定义体: StieltjesFunction.add
  zero := StieltjesFunction.const R 0
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, HeytAlg, StieltjesFunction, StieltjesFunction.add
-/
instance : AddZeroClass (StieltjesFunction R) where
  add := StieltjesFunction.add
  zero := StieltjesFunction.const R 0
  zero_add _ := ext fun _ => zero_add _
  add_zero _ := ext fun _ => add_zero _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommMonoid (StieltjesFunction R)
  body: nsmulRec n f
  add_assoc _ _ _ := ext fun _ => add_assoc _ _ _
  add_comm _ _ := ext fun _ => add_comm _ _
  __ := StieltjesFunction.instAddZeroClass

中文:
实例 :
  签名: AddCommMonoid (StieltjesFunction R)
  定义体: nsmulRec n f
  add_assoc _ _ _ := ext fun _ => add_assoc _ _ _
  add_comm _ _ := ext fun _ => add_comm _ _
  __ := StieltjesFunction.instAddZeroClass

Depends on / 依赖: nsmulRec
-/
instance : AddCommMonoid (StieltjesFunction R) where
  nsmul n f := nsmulRec n f
  add_assoc _ _ _ := ext fun _ => add_assoc _ _ _
  add_comm _ _ := ext fun _ => add_comm _ _
  __ := StieltjesFunction.instAddZeroClass

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module Real>=0 (StieltjesFunction R)
  body: {
    toFun := fun x => c * f x
    mono' := f.mono.const_mul c.2
    right_continuous' := fun x => (f.right_continuous x).const_smul c.1 }
  one_smul _ := ext fun _ => one_mul _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add _ _ _ := ext fun _ =

中文:
实例 :
  签名: Module 实数>=0 (StieltjesFunction R)
  定义体: {
    toFun := fun x => c * f x
    mono' := f.mono.const_mul c.2
    right_continuous' := fun x => (f.right_continuous x).const_smul c.1 }
  one_smul _ := ext fun _ => one_mul _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add _ _ _ := ext fun _ =

Depends on / 依赖: f.hom
-/
instance : Module Real>=0 (StieltjesFunction R) where
  smul c f := {
    toFun := fun x => c * f x
    mono' := f.mono.const_mul c.2
    right_continuous' := fun x => (f.right_continuous x).const_smul c.1 }
  one_smul _ := ext fun _ => one_mul _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _
  smul_zero _ := ext fun _ => mul_zero _
  smul_add _ _ _ := ext fun _ => mul_add _ _ _
  add_smul _ _ _ := ext fun _ => add_mul _ _ _
  zero_smul _ := ext fun _ => zero_mul _

/--
lemma `zero_apply` / 引理 `zero_apply`

English:
lemma zero_apply
  given: (x : R)
  statement: (0 : StieltjesFunction R) x = 0
  proof: rfl

中文:
引理 zero_apply
  条件: (x : R)
  结论: (0 : StieltjesFunction R) x = 0
  证明: rfl
-/
@[simp] lemma zero_apply (x : R) : (0 : StieltjesFunction R) x = 0 := rfl

/--
lemma `add_apply` / 引理 `add_apply`

English:
lemma add_apply
  given: (f g : StieltjesFunction R) (x : R)
  statement: (f + g) x = f x + g x
  proof: rfl

中文:
引理 add_apply
  条件: (f g : StieltjesFunction R) (x : R)
  结论: (f + g) x = f x + g x
  证明: rfl
-/
@[simp] lemma add_apply (f g : StieltjesFunction R) (x : R) : (f + g) x = f x + g x := rfl

/--
Definition of `_root_.Monotone.stieltjesFunction` / `_root_.Monotone.stieltjesFunction` 的定义

English:
definition _root_.Monotone.stieltjesFunction
  signature: [OrderTopology R]
  body: rightLim f
  mono' _ _ hxy := hf.rightLim hxy
  right_continuous' := by
    intro x s hs
    change forallᶠ y in 𝓝[>=] x, rightLim f y in s
    obtain ⟨l, u, hlu, lus⟩ : exists l u : Real, rightLim f x in Ioo l u ∧ Ioo l u subseteq s :=
      mem_nhds_iff_exists_Ioo_subset.1 hs
    by_cases! hx : fo

中文:
定义 _root_.Monotone.stieltjesFunction
  签名: [OrderTopology R]
  定义体: rightLim f
  mono' _ _ hxy := hf.rightLim hxy
  right_continuous' := by
    intro x s hs
    change forallᶠ y in 𝓝[>=] x, rightLim f y in s
    obtain ⟨l, u, hlu, lus⟩ : exists l u : Real, rightLim f x in Ioo l u ∧ Ioo l u subseteq s :=
      mem_nhds_iff_exists_Ioo_subset.1 hs
    by_cases! hx : fo

Depends on / 依赖: rightLim
-/
noncomputable def _root_.Monotone.stieltjesFunction [OrderTopology R]
    {f : R -> Real} (hf : Monotone f) : StieltjesFunction R where
  toFun := rightLim f
  mono' _ _ hxy := hf.rightLim hxy
  right_continuous' := by
    intro x s hs
    change forallᶠ y in 𝓝[>=] x, rightLim f y in s
    obtain ⟨l, u, hlu, lus⟩ : exists l u : Real, rightLim f x in Ioo l u ∧ Ioo l u subseteq s :=
      mem_nhds_iff_exists_Ioo_subset.1 hs
    by_cases! hx : forall y, y <= x
    · filter_upwards [self_mem_nhdsWithin] with y (hy : x <= y)
      rw [show y = x by exact le_antisymm (hx y) hy]
      exact lus hlu
    rcases hx with ⟨y₀, hy₀⟩
    obtain ⟨y, xy, h'y⟩ : exists (y : R), x < y ∧ Ioo x y subseteq f ⁻¹' Ioo l u :=
      (mem_nhdsGT_iff_exists_Ioo_subset' hy₀).1 (hf.tendsto_rightLim x (Ioo_mem_nhds hlu.1 hlu.2))
    filter_upwards [Ico_mem_nhdsGE xy] with z hz
    apply lus
    refine ⟨hlu.1.trans_le (hf.rightLim hz.1), ?_⟩
    rcases hz.1.eq_or_lt with rfl | h''z
    · exact hlu.2
    rcases Filter.eq_or_neBot (𝓝[>] z) with h'z | h'z
    · rw [rightLim_eq_of_eq_bot _ h'z]
      have : z in Ioo x y := ⟨h''z, hz.2⟩
      exact (h'y this).2
    · obtain ⟨a, za, ay⟩ : exists a : R, z < a ∧ a < y := Filter.nonempty_of_mem (Ioo_mem_nhdsGT hz.2)
      calc
        rightLim f z <= f a := hf.rightLim_le za
        _ < u := (h'y ⟨hz.1.trans_lt za, ay⟩).2

/--
theorem `_root_.Monotone.stieltjesFunction_eq` / 定理 `_root_.Monotone.stieltjesFunction_eq`

English:
theorem _root_.Monotone.stieltjesFunction_eq
  proof: rfl

中文:
定理 _root_.Monotone.stieltjesFunction_eq
  证明: rfl
-/
theorem _root_.Monotone.stieltjesFunction_eq
    [OrderTopology R] {f : R -> Real} (hf : Monotone f) (x : R) :
    hf.stieltjesFunction x = rightLim f x :=
  rfl

/--
theorem `countable_leftLim_ne` / 定理 `countable_leftLim_ne`

English:
theorem countable_leftLim_ne
  given: [OrderTopology R] (f : StieltjesFunction R)
  proof: by
  refine Countable.mono ?_ f.mono.countable_not_continuousAt
  intro x hx h'x
  apply hx
  exact (Monotone.continuousWithinAt_Iio_iff_leftLim_eq f.mono).1 h'x.continuousWithinAt

中文:
定理 countable_leftLim_ne
  条件: [OrderTopology R] (f : StieltjesFunction R)
  证明: by
  refine Countable.mono ?_ f.mono.countable_not_continuousAt
  intro x hx h'x
  apply hx
  exact (Monotone.continuousWithinAt_Iio_iff_leftLim_eq f.mono).1 h'x.continuousWithinAt

Depends on / 依赖: Countable, Countable.mono, Monotone, Monotone.continuousWithinAt_Iio_iff_leftLim_eq, continuousWithinAt, continuousWithinAt_Iio_iff_leftLim_eq, countable_not_continuousAt, f.mono, f.mono.countable_not_continuousAt, x.continuousWithinAt
-/
theorem countable_leftLim_ne [OrderTopology R] (f : StieltjesFunction R) :
    Set.Countable {x | leftLim f x != f x} := by
  refine Countable.mono ?_ f.mono.countable_not_continuousAt
  intro x hx h'x
  apply hx
  exact (Monotone.continuousWithinAt_Iio_iff_leftLim_eq f.mono).1 h'x.continuousWithinAt

/-! ### The outer measure associated to a Stieltjes function -/


open scoped Classical in
/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: (s : Set R)
  body: -- we treat separately the empty case, where the formula below would give `∞`.
  if IsEmpty R then 0
  -- if there is a bot element `x`, it does not belong to any interval `Ioc a b`. So we remove it
  -- when measuring the size of a set (the set `{x}` will have measure `0` in our construction).
  el

中文:
定义 length
  签名: (s : Set R)
  定义体: -- we treat separately the empty case, where the formula below would give `∞`.
  if IsEmpty R then 0
  -- if there is a bot element `x`, it does not belong to any interval `Ioc a b`. So we remove it
  -- when measuring the size of a set (the set `{x}` will have measure `0` in our construction).
  el
-/
def length (s : Set R) : Real>=0∞ :=
  -- we treat separately the empty case, where the formula below would give `∞`.
  if IsEmpty R then 0
  -- if there is a bot element `x`, it does not belong to any interval `Ioc a b`. So we remove it
  -- when measuring the size of a set (the set `{x}` will have measure `0` in our construction).
  else ⨅ (a) (b) (_ : s \ botSet subseteq Ioc a b), ofReal (f b - f a)

/--
lemma `length_eq` / 引理 `length_eq`

English:
lemma length_eq
  given: [Nonempty R] (s : Set R)
  proof: by
  simp [length]

中文:
引理 length_eq
  条件: [Nonempty R] (s : Set R)
  证明: by
  simp [length]

Depends on / 依赖: length
-/
lemma length_eq [Nonempty R] (s : Set R) :
    f.length s = ⨅ (a) (b) (_ : s \ botSet subseteq Ioc a b), ofReal (f b - f a) := by
  simp [length]

/--
lemma `length_eq_of_isEmpty` / 引理 `length_eq_of_isEmpty`

English:
lemma length_eq_of_isEmpty
  given: [IsEmpty R] (s : Set R)
  statement: f.length s = 0
  proof: by
  simp only [length, if_pos]

@[simp]

中文:
引理 length_eq_of_isEmpty
  条件: [IsEmpty R] (s : Set R)
  结论: f.length s = 0
  证明: by
  simp only [length, if_pos]

@[simp]

Depends on / 依赖: if_pos, length
-/
lemma length_eq_of_isEmpty [IsEmpty R] (s : Set R) : f.length s = 0 := by
  simp only [length, if_pos]

@[simp]
/--
theorem `length_empty` / 定理 `length_empty`

English:
theorem length_empty
  statement: f.length ∅ = 0
  proof: by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  inhabit R
  rw [length_eq]
exact nonpos_iff_eq_zero.1 iInf_le_of_le default iInf_le_of_le default by simp

@[simp]

中文:
定理 length_empty
  结论: f.length ∅ = 0
  证明: by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  inhabit R
  rw [length_eq]
exact nonpos_iff_eq_zero.1 iInf_le_of_le default iInf_le_of_le default by simp

@[simp]

Depends on / 依赖: iInf_le_of_le, inhabit, isEmpty_or_nonempty, length_eq, length_eq_of_isEmpty, nonpos_iff_eq_zero
-/
theorem length_empty : f.length ∅ = 0 := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  inhabit R
  rw [length_eq]
exact nonpos_iff_eq_zero.1 iInf_le_of_le default iInf_le_of_le default by simp

@[simp]
/--
theorem `length_Ioc` / 定理 `length_Ioc`

English:
theorem length_Ioc
  given: (a b : R)
  statement: f.length (Ioc a b) = ofReal (f b - f a)
  proof: by
  have : Nonempty R := ⟨a⟩
  rw [length_eq]
  refine
    le_antisymm (iInf_le_of_le a <| iInf₂_le b sdiff_subset)
      (le_iInf fun a' => le_iInf fun b' => le_iInf fun h => ENNReal.coe_le_coe.2 ?_)
  rcases le_or_gt b a with ab | ab
  · rw [Real.toNNReal_of_nonpos (sub_nonpos.2 (f.mono ab))]
   

中文:
定理 length_Ioc
  条件: (a b : R)
  结论: f.length (Ioc a b) = of实数 (f b - f a)
  证明: by
  have : Nonempty R := ⟨a⟩
  rw [length_eq]
  refine
    le_antisymm (iInf_le_of_le a <| iInf₂_le b sdiff_subset)
      (le_iInf fun a' => le_iInf fun b' => le_iInf fun h => ENNReal.coe_le_coe.2 ?_)
  rcases le_or_gt b a with ab | ab
  · rw [Real.toNNReal_of_nonpos (sub_nonpos.2 (f.mono ab))]
   

Depends on / 依赖: ENNReal, ENNReal.coe_le_coe, Ioc_sdiff_botSet, Ioc_subset_Ioc_iff, Nonempty, Real.toNNReal_of_nonpos, coe_le_coe, f.mono, iInf_le_of_le, le_antisymm, le_iInf, le_or_gt, length_eq, sdiff_subset, sub_nonpos, toNNReal_of_nonpos, zero_le
-/
theorem length_Ioc (a b : R) : f.length (Ioc a b) = ofReal (f b - f a) := by
  have : Nonempty R := ⟨a⟩
  rw [length_eq]
  refine
    le_antisymm (iInf_le_of_le a <| iInf₂_le b sdiff_subset)
      (le_iInf fun a' => le_iInf fun b' => le_iInf fun h => ENNReal.coe_le_coe.2 ?_)
  rcases le_or_gt b a with ab | ab
  · rw [Real.toNNReal_of_nonpos (sub_nonpos.2 (f.mono ab))]
    apply zero_le
  simp only [Ioc_sdiff_botSet] at h
  obtain ⟨h₁, h₂⟩ := (Ioc_subset_Ioc_iff ab).1 h
  grw [h₁, h₂]

@[gcongr]
/--
theorem `length_mono` / 定理 `length_mono`

English:
theorem length_mono
  given: {s₁ s₂ : Set R} (h : s₁ subseteq s₂)
  statement: f.length s₁ <= f.length s₂
  proof: by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  simp only [length_eq]
  exact iInf_mono fun a => biInf_mono fun b => by gcongr

中文:
定理 length_mono
  条件: {s₁ s₂ : Set R} (h : s₁ subseteq s₂)
  结论: f.length s₁ <= f.length s₂
  证明: by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  simp only [length_eq]
  exact iInf_mono fun a => biInf_mono fun b => by gcongr

Depends on / 依赖: biInf_mono, iInf_mono, isEmpty_or_nonempty, length_eq, length_eq_of_isEmpty
-/
theorem length_mono {s₁ s₂ : Set R} (h : s₁ subseteq s₂) : f.length s₁ <= f.length s₂ := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  simp only [length_eq]
  exact iInf_mono fun a => biInf_mono fun b => by gcongr

/--
theorem `length_sdiff_botSet` / 定理 `length_sdiff_botSet`

English:
theorem length_sdiff_botSet
  given: {s : Set R}
  statement: f.length (s \ botSet) = f.length s
  proof: by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  · simp [length_eq]

@[deprecated (since := "2026-06-03")] alias length_diff_botSet := length_sdiff_botSet

中文:
定理 length_sdiff_botSet
  条件: {s : Set R}
  结论: f.length (s \ botSet) = f.length s
  证明: by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  · simp [length_eq]

@[deprecated (since := "2026-06-03")] alias length_diff_botSet := length_sdiff_botSet

Depends on / 依赖: isEmpty_or_nonempty, length_eq, length_eq_of_isEmpty
-/
theorem length_sdiff_botSet {s : Set R} : f.length (s \ botSet) = f.length s := by
  rcases isEmpty_or_nonempty R with hR | hR
  · simp [length_eq_of_isEmpty]
  · simp [length_eq]

@[deprecated (since := "2026-06-03")] alias length_diff_botSet := length_sdiff_botSet

open MeasureTheory

/--
Definition of `outer` / `outer` 的定义

English:
definition outer
  signature: : OuterMeasure R
  body: OuterMeasure.ofFunction f.length f.length_empty

中文:
定义 outer
  签名: : OuterMeasure R
  定义体: OuterMeasure.ofFunction f.length f.length_empty
-/
protected def outer : OuterMeasure R :=
  OuterMeasure.ofFunction f.length f.length_empty

/--
theorem `outer_le_length` / 定理 `outer_le_length`

English:
theorem outer_le_length
  given: (s : Set R)
  statement: f.outer s <= f.length s
  proof: OuterMeasure.ofFunction_le _

中文:
定理 outer_le_length
  条件: (s : Set R)
  结论: f.outer s <= f.length s
  证明: OuterMeasure.ofFunction_le _

Depends on / 依赖: OuterMeasure, OuterMeasure.ofFunction_le, ofFunction_le
-/
theorem outer_le_length (s : Set R) : f.outer s <= f.length s :=
  OuterMeasure.ofFunction_le _

variable [OrderTopology R] [CompactIccSpace R]

/--
theorem `length_subadditive_Icc_Ioo` / 定理 `length_subadditive_Icc_Ioo`

English:
theorem length_subadditive_Icc_Ioo
  given: {a b : R} {c d : Nat -> R} (ss : Icc a b subseteq ⋃ i, Iotop (c i) (d i))
  proof: by
  suffices
    forall (s : Finset Nat) (b), Icc a b subseteq (⋃ i in (s : Set Nat), Iotop (c i) (d i)) ->
      (ofReal (f b - f a) : Real>=0∞) <= ∑ i in s, ofReal (f (d i) - f (c i)) by
    rcases isCompact_Icc.elim_finite_subcover_image
        (fun (i : Nat) (_ : i in univ) => @isOpen_Iotop _ 

中文:
定理 length_subadditive_Icc_Ioo
  条件: {a b : R} {c d : 自然数 -> R} (ss : Icc a b subseteq ⋃ i, Iotop (c i) (d i))
  证明: by
  suffices
    forall (s : Finset Nat) (b), Icc a b subseteq (⋃ i in (s : Set Nat), Iotop (c i) (d i)) ->
      (ofReal (f b - f a) : Real>=0∞) <= ∑ i in s, ofReal (f (d i) - f (c i)) by
    rcases isCompact_Icc.elim_finite_subcover_image
        (fun (i : Nat) (_ : i in univ) => @isOpen_Iotop _ 

Depends on / 依赖: ENNReal, ENNReal.ts, Finite, Finite.mem_toFinset, Finset, Finset.set_biUnion_coe, elim_finite_subcover_image, hf.toFinset, isCompact_Icc, isCompact_Icc.elim_finite_subcover_image, isOpen_Iotop, mem_toFinset, ofReal, set_biUnion_coe, subseteq, toFinset
-/
theorem length_subadditive_Icc_Ioo {a b : R} {c d : Nat -> R} (ss : Icc a b subseteq ⋃ i, Iotop (c i) (d i)) :
    ofReal (f b - f a) <= ∑' i, ofReal (f (d i) - f (c i)) := by
  suffices
    forall (s : Finset Nat) (b), Icc a b subseteq (⋃ i in (s : Set Nat), Iotop (c i) (d i)) ->
      (ofReal (f b - f a) : Real>=0∞) <= ∑ i in s, ofReal (f (d i) - f (c i)) by
    rcases isCompact_Icc.elim_finite_subcover_image
        (fun (i : Nat) (_ : i in univ) => @isOpen_Iotop _ _ _ _ (c i) (d i)) (by simpa using ss) with
      ⟨s, _, hf, hs⟩
    have e : ⋃ i in (hf.toFinset : Set Nat), Iotop (c i) (d i) = ⋃ i in s, Iotop (c i) (d i) := by
      simp only [Finset.set_biUnion_coe,
        Finite.mem_toFinset]
    rw [ENNReal.tsum_eq_iSup_sum]
    refine le_trans ?_ (le_iSup _ hf.toFinset)
    exact this hf.toFinset _ (by simpa only [e])
  clear ss b
  refine fun s => Finset.strongInductionOn s fun s IH b cv => ?_
  rcases le_total b a with ab | ab
  · rw [ENNReal.ofReal_eq_zero.2 (sub_nonpos.2 (f.mono ab))]
    exact zero_le
  obtain ⟨i, is, bcd⟩ : exists i in s, b in Iotop (c i) (d i) := by
    simpa only [SetLike.mem_coe, mem_iUnion, exists_prop] using cv ⟨ab, le_rfl⟩
  rw [← Finset.insert_erase is] at cv ⊢
  rw [Finset.coe_insert]; rw [biUnion_insert] at cv
  rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  replace bcd : b in Ioc (c i) (d i) := Iotop_subset_Ioc bcd
  grw [← IH _ (Finset.erase_ssubset is) (c i), ← ENNReal.ofReal_add_le]
  · rw [sub_add_sub_cancel]
    grw [bcd.2]
  · rintro x ⟨h₁, h₂⟩
    apply (cv ⟨h₁, le_trans h₂ (le_of_lt bcd.1)⟩).resolve_left (fun h => ?_)
    order [(Iotop_subset_Ioc h).1]

@[simp]
/--
theorem `outer_Ioc` / 定理 `outer_Ioc`

English:
theorem outer_Ioc
  given: [DenselyOrdered R] (a b : R)
  statement: f.outer (Ioc a b) = ofReal (f b - f a)
  proof: by
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
    by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
    intervals, while we would like to have a compact interval covered by open intervals to use
    c

中文:
定理 outer_Ioc
  条件: [DenselyOrdered R] (a b : R)
  结论: f.outer (Ioc a b) = of实数 (f b - f a)
  证明: by
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
    by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
    intervals, while we would like to have a compact interval covered by open intervals to use
    c
-/
theorem outer_Ioc [DenselyOrdered R] (a b : R) : f.outer (Ioc a b) = ofReal (f b - f a) := by
  /- It suffices to show that, if `(a, b]` is covered by sets `s i`, then `f b - f a` is bounded
    by `∑ f.length (s i) + ε`. The difficulty is that `f.length` is expressed in terms of half-open
    intervals, while we would like to have a compact interval covered by open intervals to use
    compactness and finite sums, as provided by `length_subadditive_Icc_Ioo`. The trick is to use
    the right-continuity of `f`. If `a'` is close enough to `a` on its right, then `[a', b]` is
    still covered by the sets `s i` and moreover `f b - f a'` is very close to `f b - f a`
    (up to `ε/2`).
    Also, by definition one can cover `s i` by a half-closed interval `(p i, q i]` with `f`-length
    very close to that of `s i` (within a suitably small `ε' i`, say). If one moves `q i` very
    slightly to the right, then the `f`-length will change very little by right continuity, and we
    will get an open interval `(p i, q' i)` covering `s i` with `f (q' i) - f (p i)` within `ε' i`
    of the `f`-length of `s i`. This is not possible if `q i` is top, but this is not an issue
    as the interval `(p i, q i]` is already open in this case. However, this means that we can
    not use `Ioo` in this proof -- instead, we use `Iotop` precisely to avoid this issue. -/
  refine le_antisymm ?_ ?_
  · rw [← f.length_Ioc]
    apply outer_le_length
  rcases le_or_gt b a with hab | hab
  · have : ofReal (f b - f a) = 0 := by simpa using f.mono hab
    simp [this]
  apply (le_iInf₂ fun s hs => ENNReal.le_of_forall_pos_le_add fun ε εpos h => ?_)
  let δ := ε / 2
  have δpos : 0 < (δ : Real>=0∞) := by simpa [δ] using εpos.ne'
  rcases ENNReal.exists_pos_sum_of_countable δpos.ne' Nat with ⟨ε', ε'0, hε⟩
  obtain ⟨a', ha', aa'⟩ : exists a', f a' - f a < δ ∧ a < a' := by
    have A : ContinuousWithinAt (fun r => f r - f a) (Ioi a) a := by
      refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
      exact (f.right_continuous a).mono Ioi_subset_Ici_self
    have B : f a - f a < δ := by rwa [sub_self, NNReal.coe_pos, ← ENNReal.coe_pos]
    have : (𝓝[>] a).NeBot := nhdsGT_neBot_of_exists_gt ⟨b, hab⟩
    exact (((tendsto_order.1 A).2 _ B).and self_mem_nhdsWithin).exists
  have : Nonempty R := ⟨a⟩
  have : forall i, exists p : R × R, Icc a' b inter s i subseteq Iotop p.1 p.2 ∧
      (ofReal (f p.2 - f p.1) : Real>=0∞) < f.length (s i) + ε' i := by
    intro i
    have hl :=
      ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_ne_zero.2 (ε'0 i).ne')
    conv at hl =>
      lhs
      rw [length_eq]
    simp only [iInf_lt_iff, exists_prop] at hl
    rcases hl with ⟨p, q', spq, hq'⟩
    have A : Icc a' b inter s i subseteq Ioc p q' := by
      rintro x ⟨hx, h'x⟩
      apply spq
      simp [h'x, notMem_botSet_of_lt (aa'.trans_le hx.1)]
    by_cases htq' : IsTop q'
    · refine ⟨(p, q'), ?_, hq'⟩
      rintro x hx
      simp only [Iotop, htq', ↓reduceIte, mem_Ioc]
      exact ⟨(A hx).1, htq' _⟩
    have : (𝓝[>] q').NeBot := by simp [Filter.neBot_iff, nhdsGT_eq_bot_iff, htq', not_covBy]
    have : ContinuousWithinAt (fun r => ofReal (f r - f p)) (Ioi q') q' := by
      apply ENNReal.continuous_ofReal.continuousAt.comp_continuousWithinAt
      refine ContinuousWithinAt.sub ?_ continuousWithinAt_const
      exact (f.right_continuous q').mono Ioi_subset_Ici_self
    rcases (((tendsto_order.1 this).2 _ hq').and self_mem_nhdsWithin).exists with ⟨q, hq, q'q⟩
    exact ⟨⟨p, q⟩, A.trans ((Ioc_subset_Ioo_right q'q).trans Ioo_subset_Iotop), hq⟩
  choose g hg using this
  have I_subset : Icc a' b subseteq ⋃ i, Iotop (g i).1 (g i).2 :=
    calc
      Icc a' b subseteq Icc a' b inter Ioc a b := fun x hx => ⟨hx, aa'.trans_le hx.1, hx.2⟩
      _ subseteq Icc a' b inter ⋃ i, s i := by gcongr
      _ = ⋃ i, Icc a' b inter s i := inter_iUnion (Icc a' b) s
      _ subseteq ⋃ i, Iotop (g i).1 (g i).2 := iUnion_mono fun i => (hg i).1
  calc
    ofReal (f b - f a) = ofReal (f b - f a' + (f a' - f a)) := by rw [sub_add_sub_cancel]
    _ <= ofReal (f b - f a') + ofReal (f a' - f a) := ENNReal.ofReal_add_le
    _ <= ∑' i, ofReal (f (g i).2 - f (g i).1) + ofReal δ :=
      (add_le_add (f.length_subadditive_Icc_Ioo I_subset) (ENNReal.ofReal_le_ofReal ha'.le))
    _ <= ∑' i, (f.length (s i) + ε' i) + δ :=
      (add_le_add (ENNReal.tsum_le_tsum fun i => (hg i).2.le)
        (by simp only [ENNReal.ofReal_coe_nnreal, le_rfl]))
    _ = ∑' i, f.length (s i) + ∑' i, (ε' i : Real>=0∞) + δ := by rw [ENNReal.tsum_add]
    _ <= ∑' i, f.length (s i) + δ + δ := add_le_add (add_le_add le_rfl hε.le) le_rfl
    _ = ∑' i : Nat, f.length (s i) + ε := by simp [δ, add_assoc, ENNReal.add_halves]

omit [OrderTopology R] [CompactIccSpace R] in
/--
theorem `measurableSet_Ioi` / 定理 `measurableSet_Ioi`

English:
theorem measurableSet_Ioi
  given: {c : R}
  statement: MeasurableSet[f.outer.caratheodory] (Ioi c)
  proof: by
  refine OuterMeasure.ofFunction_caratheodory fun t => ?_
  have : Nonempty R := ⟨c⟩
  simp only [length_eq]
  refine le_iInf fun a => le_iInf fun b => le_iInf fun h => ?_
  simp only [← length_eq]
  rw [← length_sdiff_botSet]; rw [inter_sdiff_right_comm]; rw [← length_sdiff_botSet (s := t \ Ioi 

中文:
定理 measurableSet_Ioi
  条件: {c : R}
  结论: MeasurableSet[f.outer.caratheodory] (Ioi c)
  证明: by
  refine OuterMeasure.ofFunction_caratheodory fun t => ?_
  have : Nonempty R := ⟨c⟩
  simp only [length_eq]
  refine le_iInf fun a => le_iInf fun b => le_iInf fun h => ?_
  simp only [← length_eq]
  rw [← length_sdiff_botSet]; rw [inter_sdiff_right_comm]; rw [← length_sdiff_botSet (s := t \ Ioi 

Depends on / 依赖: Ioc_eq_empty, Ioc_inter_Ioi, Nonempty, OuterMeasure, OuterMeasure.ofFunction_caratheodory, f.length_Ioc, inter_sdiff_right_comm, le_iInf, le_refl, le_total, length_Ioc, length_eq, length_sdiff_botSet, max_eq_right, min_eq_left, ofFunction_caratheodory, sdiff_sdiff_comm
-/
theorem measurableSet_Ioi {c : R} : MeasurableSet[f.outer.caratheodory] (Ioi c) := by
  refine OuterMeasure.ofFunction_caratheodory fun t => ?_
  have : Nonempty R := ⟨c⟩
  simp only [length_eq]
  refine le_iInf fun a => le_iInf fun b => le_iInf fun h => ?_
  simp only [← length_eq]
  rw [← length_sdiff_botSet]; rw [inter_sdiff_right_comm]; rw [← length_sdiff_botSet (s := t \ Ioi c)]; rw [sdiff_sdiff_comm]
  grw [h]
  rcases le_total a c with hac | hac <;> rcases le_total b c with hbc | hbc
  · simp only [Ioc_inter_Ioi, f.length_Ioc, hac, hbc, le_refl, Ioc_eq_empty,
      max_eq_right, min_eq_left, Ioc_sdiff_Ioi, f.length_empty, zero_add, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_sdiff_Ioi, f.length_Ioc, min_eq_right,
      ← ENNReal.ofReal_add, f.mono hac, f.mono hbc, sub_nonneg,
      sub_add_sub_cancel, le_refl,
      max_eq_right]
  · simp only [hbc, le_refl, Ioc_eq_empty, Ioc_inter_Ioi, min_eq_left, Ioc_sdiff_Ioi,
      f.length_empty, zero_add, or_true, le_sup_iff, f.length_Ioc, not_lt]
  · simp only [hac, hbc, Ioc_inter_Ioi, Ioc_sdiff_Ioi, f.length_Ioc, min_eq_right,
      le_refl, Ioc_eq_empty, add_zero, max_eq_left, f.length_empty, not_lt]

/--
theorem `outer_trim` / 定理 `outer_trim`

English:
theorem outer_trim
  given: [MeasurableSpace R] [BorelSpace R] [DenselyOrdered R]
  proof: by
  refine le_antisymm (fun s => ?_) (OuterMeasure.le_trim _)
  rw [OuterMeasure.trim_eq_iInf]
  refine le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' Nat with ⟨ε', ε'0, hε⟩
  grw [← hε]
  r

中文:
定理 outer_trim
  条件: [MeasurableSpace R] [BorelSpace R] [DenselyOrdered R]
  证明: by
  refine le_antisymm (fun s => ?_) (OuterMeasure.le_trim _)
  rw [OuterMeasure.trim_eq_iInf]
  refine le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' Nat with ⟨ε', ε'0, hε⟩
  grw [← hε]
  r

Depends on / 依赖: ENNReal, ENNReal.coe_pos, ENNReal.exists_pos_sum_of_countable, ENNReal.le_of_forall_pos_le_add, ENNReal.tsum_add, MeasurableSet, OuterMeasure, OuterMeasure.le_trim, OuterMeasure.trim_eq_iInf, coe_pos, exists_pos_sum_of_countable, f.length, f.outer, isEmpty_or_nonempty, le_antisymm, le_iInf, le_of_forall_pos_le_add, le_trim, length, ofReal
-/
theorem outer_trim [MeasurableSpace R] [BorelSpace R] [DenselyOrdered R] :
    f.outer.trim = f.outer := by
  refine le_antisymm (fun s => ?_) (OuterMeasure.le_trim _)
  rw [OuterMeasure.trim_eq_iInf]
  refine le_iInf fun t => le_iInf fun ht => ENNReal.le_of_forall_pos_le_add fun ε ε0 h => ?_
  rcases ENNReal.exists_pos_sum_of_countable (ENNReal.coe_pos.2 ε0).ne' Nat with ⟨ε', ε'0, hε⟩
  grw [← hε]
  rw [← ENNReal.tsum_add]
  choose g hg using
    show forall i, exists s, t i subseteq s ∧ MeasurableSet s ∧ f.outer s <= f.length (t i) + ofReal (ε' i) by
      intro i
      rcases isEmpty_or_nonempty R with hR | hR
      · exact ⟨∅, by simp, MeasurableSet.empty, by simp⟩
      have hl :=
        ENNReal.lt_add_right ((ENNReal.le_tsum i).trans_lt h).ne (ENNReal.coe_pos.2 (ε'0 i)).ne'
      conv at hl =>
        lhs
        rw [length_eq]
      simp only [iInf_lt_iff] at hl
      rcases hl with ⟨a, b, h₁, h₂⟩
      rw [← f.outer_Ioc] at h₂
      rw [sdiff_subset_iff] at h₁
      refine ⟨_, h₁, measurableSet_botSet.union measurableSet_Ioc, le_of_lt ?_⟩
      calc f.outer (botSet union Ioc a b)
      _ <= f.outer botSet + f.outer (Ioc a b) := measure_union_le _ _
      _ <= f.length botSet + f.outer (Ioc a b) := by gcongr; apply outer_le_length
      _ = 0 + f.outer (Ioc a b) := by
        simp only [← length_sdiff_botSet, sdiff_self, empty_sdiff, outer_Ioc, zero_add]
        simp [empty_sdiff]
      _ = f.outer (Ioc a b) := by simp
      _ < f.length (t i) + ofReal ↑(ε' i) := by simpa using h₂
  simp only [ofReal_coe_nnreal] at hg
  apply iInf_le_of_le (iUnion g) _
  apply iInf_le_of_le (ht.trans <| iUnion_mono fun i => (hg i).1) _
  apply iInf_le_of_le (MeasurableSet.iUnion fun i => (hg i).2.1) _
  exact le_trans (measure_iUnion_le _) (ENNReal.tsum_le_tsum fun i => (hg i).2.2)

omit [CompactIccSpace R] in
/--
theorem `borel_le_measurable` / 定理 `borel_le_measurable`

English:
theorem borel_le_measurable
  given: [SecondCountableTopology R]
  proof: by
  rw [borel_eq_generateFrom_Ioi]
  refine MeasurableSpace.generateFrom_le ?_
  simp +contextual [f.measurableSet_Ioi]

中文:
定理 borel_le_measurable
  条件: [SecondCountableTopology R]
  证明: by
  rw [borel_eq_generateFrom_Ioi]
  refine MeasurableSpace.generateFrom_le ?_
  simp +contextual [f.measurableSet_Ioi]

Depends on / 依赖: MeasurableSpace, MeasurableSpace.generateFrom_le, borel_eq_generateFrom_Ioi, contextual, f.measurableSet_Ioi, generateFrom_le, measurableSet_Ioi
-/
theorem borel_le_measurable [SecondCountableTopology R] :
    borel R <= f.outer.caratheodory := by
  rw [borel_eq_generateFrom_Ioi]
  refine MeasurableSpace.generateFrom_le ?_
  simp +contextual [f.measurableSet_Ioi]

/-! ### The measure associated to a Stieltjes function -/

variable [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] [DenselyOrdered R]

/-- The measure associated to a Stieltjes function, giving mass `f b - f a` to the
interval `(a, b]`. If there is a bot element, it gives zero mass to it. -/
protected irreducible_def measure : Measure R where
  toOuterMeasure := f.outer
m_iUnion _s hs := f.outer.iUnion_eq_of_caratheodory fun i => f.borel_le_measurable _ by
    borelize R
    exact hs i
  trim_le := f.outer_trim.le

@[simp]
/--
theorem `measure_Ioc` / 定理 `measure_Ioc`

English:
theorem measure_Ioc
  given: (a b : R)
  statement: f.measure (Ioc a b) = ofReal (f b - f a)
  proof: by
  rw [StieltjesFunction.measure]
  exact f.outer_Ioc a b

@[simp]

中文:
定理 measure_Ioc
  条件: (a b : R)
  结论: f.measure (Ioc a b) = of实数 (f b - f a)
  证明: by
  rw [StieltjesFunction.measure]
  exact f.outer_Ioc a b

@[simp]

Depends on / 依赖: StieltjesFunction, StieltjesFunction.measure, f.outer_Ioc, measure, outer_Ioc
-/
theorem measure_Ioc (a b : R) : f.measure (Ioc a b) = ofReal (f b - f a) := by
  rw [StieltjesFunction.measure]
  exact f.outer_Ioc a b

@[simp]
/--
theorem `measure_singleton` / 定理 `measure_singleton`

English:
theorem measure_singleton
  given: (a : R)
  statement: f.measure {a} = ofReal (f a - leftLim f a)
  proof: by
  by_cases ha : IsBot a
  · have : leftLim f a = f a := by
      apply leftLim_eq_of_eq_bot
      simp [nhdsLT_eq_bot_iff, ha]
    simp only [this, sub_self, ofReal_zero]
    apply eq_bot_iff.2
    rw [StieltjesFunction.measure]
    apply (outer_le_length _ _).trans
    rw [← length_sdiff_botSet]

中文:
定理 measure_singleton
  条件: (a : R)
  结论: f.measure {a} = of实数 (f a - leftLim f a)
  证明: by
  by_cases ha : IsBot a
  · have : leftLim f a = f a := by
      apply leftLim_eq_of_eq_bot
      simp [nhdsLT_eq_bot_iff, ha]
    simp only [this, sub_self, ofReal_zero]
    apply eq_bot_iff.2
    rw [StieltjesFunction.measure]
    apply (outer_le_length _ _).trans
    rw [← length_sdiff_botSet]

Depends on / 依赖: StieltjesFunction, StieltjesFunction.measure, StrictMono, eq_bot_iff, eq_singleton_of_mem, leftLim, leftLim_eq_of_eq_bot, length_sdiff_botSet, measure, nhdsLT_eq_bot_iff, not_forall, not_le, ofReal_zero, outer_le_length, sub_self, subsingleton_botSet, subsingleton_botSet.eq_singleton_of_mem, u_lim, u_lt_a, u_mono
-/
theorem measure_singleton (a : R) : f.measure {a} = ofReal (f a - leftLim f a) := by
  by_cases ha : IsBot a
  · have : leftLim f a = f a := by
      apply leftLim_eq_of_eq_bot
      simp [nhdsLT_eq_bot_iff, ha]
    simp only [this, sub_self, ofReal_zero]
    apply eq_bot_iff.2
    rw [StieltjesFunction.measure]
    apply (outer_le_length _ _).trans
    rw [← length_sdiff_botSet]
    simp [subsingleton_botSet.eq_singleton_of_mem ha]
  obtain ⟨b, hb⟩ : exists b, b < a := by simpa only [IsBot, not_forall, not_le] using ha
  obtain ⟨u, u_mono, u_lt_a, u_lim⟩ :
    exists u : Nat -> R, StrictMono u ∧ (forall n : Nat, u n in Ioo b a) ∧ Tendsto u atTop (𝓝 a) :=
    exists_seq_strictMono_tendsto' hb
  replace u_lt_a n : u n < a := (u_lt_a n).2
  have A : {a} = ⋂ n, Ioc (u n) a := by
    refine Subset.antisymm (fun x hx => by simp [mem_singleton_iff.1 hx, u_lt_a]) fun x hx => ?_
    replace hx : forall (i : Nat), u i < x ∧ x <= a := by simpa using hx
    have : a <= x := le_of_tendsto' u_lim fun n => (hx n).1.le
    simp [le_antisymm this (hx 0).2]
  have L1 : Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (f.measure {a})) := by
    rw [A]
    refine tendsto_measure_iInter_atTop (fun n => nullMeasurableSet_Ioc)
      (fun m n hmn => ?_) ?_
    · exact Ioc_subset_Ioc_left (u_mono.monotone hmn)
    · exact ⟨0, by simpa only [measure_Ioc] using ENNReal.ofReal_ne_top⟩
  have L2 :
      Tendsto (fun n => f.measure (Ioc (u n) a)) atTop (𝓝 (ofReal (f a - leftLim f a))) := by
    simp only [measure_Ioc]
    have : Tendsto (fun n => f (u n)) atTop (𝓝 (leftLim f a)) := by
      apply (f.mono.tendsto_leftLim a).comp
      exact
        tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ u_lim
          (Eventually.of_forall fun n => u_lt_a n)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.sub this)
  exact tendsto_nhds_unique L1 L2

@[simp]
/--
theorem `measure_Icc` / 定理 `measure_Icc`

English:
theorem measure_Icc
  given: (a b : R)
  statement: f.measure (Icc a b) = ofReal (f b - leftLim f a)
  proof: by
  rcases le_or_gt a b with (hab | hab)
  · have A : Disjoint {a} (Ioc a b) := by simp
    simp [← Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ← ENNReal.ofReal_add,
      f.mono.leftLim_le, measure_union A measurableSet_Ioc, f.mono hab]
  · simp only [hab, measure_empty, Icc_eq_empty, not_l

中文:
定理 measure_Icc
  条件: (a b : R)
  结论: f.measure (Icc a b) = of实数 (f b - leftLim f a)
  证明: by
  rcases le_or_gt a b with (hab | hab)
  · have A : Disjoint {a} (Ioc a b) := by simp
    simp [← Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ← ENNReal.ofReal_add,
      f.mono.leftLim_le, measure_union A measurableSet_Ioc, f.mono hab]
  · simp only [hab, measure_empty, Icc_eq_empty, not_l

Depends on / 依赖: Disjoint, ENNReal, ENNReal.ofReal_add, ENNReal.ofReal_eq_zero, Icc_eq_empty, Icc_union_Ioc_eq_Icc, f.mono, f.mono.le_leftLim, f.mono.leftLim_le, le_leftLim, le_or_gt, le_rfl, leftLim_le, measurableSet_Ioc, measure_empty, measure_union, not_le, ofReal_add, ofReal_eq_zero, singleton_union
-/
theorem measure_Icc (a b : R) : f.measure (Icc a b) = ofReal (f b - leftLim f a) := by
  rcases le_or_gt a b with (hab | hab)
  · have A : Disjoint {a} (Ioc a b) := by simp
    simp [← Icc_union_Ioc_eq_Icc le_rfl hab, -singleton_union, ← ENNReal.ofReal_add,
      f.mono.leftLim_le, measure_union A measurableSet_Ioc, f.mono hab]
  · simp only [hab, measure_empty, Icc_eq_empty, not_le]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.le_leftLim hab]

@[simp]
/--
theorem `measure_Ioo` / 定理 `measure_Ioo`

English:
theorem measure_Ioo
  given: {a b : R}
  statement: f.measure (Ioo a b) = ofReal (leftLim f b - f a)
  proof: by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ioo_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim_le hab]
  · have A : Disjoint (Ioo a b) {b} := by simp
    have D : f b - f a = f b - leftLim f b + (leftLim f b - f a) := by abel
    have := 

中文:
定理 measure_Ioo
  条件: {a b : R}
  结论: f.measure (Ioo a b) = of实数 (leftLim f b - f a)
  证明: by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ioo_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim_le hab]
  · have A : Disjoint (Ioo a b) {b} := by simp
    have D : f b - f a = f b - leftLim f b + (leftLim f b - f a) := by abel
    have := 

Depends on / 依赖: Disjoint, ENNReal, ENNReal.ofReal_add, ENNReal.ofReal_eq_zero, Icc_self, Ioo_eq_empty, Ioo_union_Icc_eq_Ioc, add_comm, f.measure_Ioc, f.mono.leftLim_le, le_or_gt, le_rfl, leftLim, leftLim_le, measurableSet_singleton, measure_Ioc, measure_empty, measure_singleton, measure_union, not_lt
-/
theorem measure_Ioo {a b : R} : f.measure (Ioo a b) = ofReal (leftLim f b - f a) := by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ioo_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim_le hab]
  · have A : Disjoint (Ioo a b) {b} := by simp
    have D : f b - f a = f b - leftLim f b + (leftLim f b - f a) := by abel
    have := f.measure_Ioc a b
    simp only [← Ioo_union_Icc_eq_Ioc hab le_rfl, measure_singleton,
      measure_union A (measurableSet_singleton b), Icc_self] at this
    rw [D]; rw [ENNReal.ofReal_add]; rw [add_comm] at this
    · simpa only [ENNReal.add_right_inj ENNReal.ofReal_ne_top]
    · simp only [f.mono.leftLim_le le_rfl, sub_nonneg]
    · simp only [f.mono.le_leftLim hab, sub_nonneg]

@[simp]
/--
theorem `measure_Ico` / 定理 `measure_Ico`

English:
theorem measure_Ico
  given: (a b : R)
  statement: f.measure (Ico a b) = ofReal (leftLim f b - leftLim f a)
  proof: by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ico_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim hab]
  · have A : Disjoint {a} (Ioo a b) := by simp
    simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, f.mono.leftLim_le,
      mea

中文:
定理 measure_Ico
  条件: (a b : R)
  结论: f.measure (Ico a b) = of实数 (leftLim f b - leftLim f a)
  证明: by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ico_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim hab]
  · have A : Disjoint {a} (Ioo a b) := by simp
    simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, f.mono.leftLim_le,
      mea

Depends on / 依赖: Disjoint, ENNReal, ENNReal.ofReal_add, ENNReal.ofReal_eq_zero, Icc_union_Ioo_eq_Ico, Ico_eq_empty, f.mono.le_leftLim, f.mono.leftLim, f.mono.leftLim_le, le_leftLim, le_or_gt, le_rfl, leftLim, leftLim_le, measurableSet_Ioo, measure_empty, measure_union, not_lt, ofReal_add, ofReal_eq_zero
-/
theorem measure_Ico (a b : R) : f.measure (Ico a b) = ofReal (leftLim f b - leftLim f a) := by
  rcases le_or_gt b a with (hab | hab)
  · simp only [hab, measure_empty, Ico_eq_empty, not_lt]
    symm
    simp [ENNReal.ofReal_eq_zero, f.mono.leftLim hab]
  · have A : Disjoint {a} (Ioo a b) := by simp
    simp [← Icc_union_Ioo_eq_Ico le_rfl hab, -singleton_union, f.mono.leftLim_le,
      measure_union A measurableSet_Ioo, f.mono.le_leftLim hab, ← ENNReal.ofReal_add]

@[simp]
/--
theorem `measure_botSet` / 定理 `measure_botSet`

English:
theorem measure_botSet
  statement: f.measure botSet = 0
  proof: by
  by_cases! hx : exists x : R, IsBot x
  · simp [botSet_eq_singleton_of_isBot hx.choose_spec, leftLim_eq_of_isBot hx.choose_spec]
  · simp [botSet, hx]

中文:
定理 measure_botSet
  结论: f.measure botSet = 0
  证明: by
  by_cases! hx : exists x : R, IsBot x
  · simp [botSet_eq_singleton_of_isBot hx.choose_spec, leftLim_eq_of_isBot hx.choose_spec]
  · simp [botSet, hx]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, botSet, botSet_eq_singleton_of_isBot, choose_spec, hx.choose_spec, leftLim_eq_of_isBot
-/
theorem measure_botSet : f.measure botSet = 0 := by
  by_cases! hx : exists x : R, IsBot x
  · simp [botSet_eq_singleton_of_isBot hx.choose_spec, leftLim_eq_of_isBot hx.choose_spec]
  · simp [botSet, hx]

/--
theorem `measure_Iic` / 定理 `measure_Iic`

English:
theorem measure_Iic
  given: {l : Real} (hf : Tendsto f atBot (𝓝 l)) (x : R)
  proof: by
  have : Nonempty R := ⟨x⟩
  cases botOrderOrNoBotOrder R
  · have : Iic x = Icc ⊥ x := by simp
    rw [atBot_eq_pure_of_isBot isBot_bot] at hf
    rw [this]; rw [measure_Icc]; rw [leftLim_eq_of_isBot isBot_bot]; rw [tendsto_nhds_unique hf (tendsto_pure_nhds f ⊥)]
  have : NoMinOrder R := NoBotOr

中文:
定理 measure_Iic
  条件: {l : 实数} (hf : Tendsto f atBot (𝓝 l)) (x : R)
  证明: by
  have : Nonempty R := ⟨x⟩
  cases botOrderOrNoBotOrder R
  · have : Iic x = Icc ⊥ x := by simp
    rw [atBot_eq_pure_of_isBot isBot_bot] at hf
    rw [this]; rw [measure_Icc]; rw [leftLim_eq_of_isBot isBot_bot]; rw [tendsto_nhds_unique hf (tendsto_pure_nhds f ⊥)]
  have : NoMinOrder R := NoBotOr

Depends on / 依赖: ENNReal, ENNReal.tendsto_ofReal, NoBotOrder, NoBotOrder.to_noMinOrder, NoMinOrder, Nonempty, Tendsto, Tendsto.const_sub, atBot_eq_pure_of_isBot, botOrderOrNoBotOrder, const_sub, isBot_bot, leftLim_eq_of_isBot, measure_Icc, measure_Ioc, simp_rw, tendsto_measure_Ioc_atBot, tendsto_nhds_unique, tendsto_ofReal, tendsto_pure_nhds
-/
theorem measure_Iic {l : Real} (hf : Tendsto f atBot (𝓝 l)) (x : R) :
    f.measure (Iic x) = ofReal (f x - l) := by
  have : Nonempty R := ⟨x⟩
  cases botOrderOrNoBotOrder R
  · have : Iic x = Icc ⊥ x := by simp
    rw [atBot_eq_pure_of_isBot isBot_bot] at hf
    rw [this]; rw [measure_Icc]; rw [leftLim_eq_of_isBot isBot_bot]; rw [tendsto_nhds_unique hf (tendsto_pure_nhds f ⊥)]
  have : NoMinOrder R := NoBotOrder.to_noMinOrder R
  refine tendsto_nhds_unique (tendsto_measure_Ioc_atBot _ _) ?_
  simp_rw [measure_Ioc]
  exact ENNReal.tendsto_ofReal (Tendsto.const_sub _ hf)

/--
lemma `measure_Iio` / 引理 `measure_Iio`

English:
lemma measure_Iio
  given: {l : Real} (hf : Tendsto f atBot (𝓝 l)) (x : R)
  proof: by
  have : Nonempty R := ⟨x⟩
  rw [← Iic_sdiff_right]; rw [measure_sdiff _ (nullMeasurableSet_singleton x)]; rw [measure_singleton]; rw [f.measure_Iic hf]; rw [← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp

中文:
引理 measure_Iio
  条件: {l : 实数} (hf : Tendsto f atBot (𝓝 l)) (x : R)
  证明: by
  have : Nonempty R := ⟨x⟩
  rw [← Iic_sdiff_right]; rw [measure_sdiff _ (nullMeasurableSet_singleton x)]; rw [measure_singleton]; rw [f.measure_Iic hf]; rw [← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp

Depends on / 依赖: Iic_sdiff_right, Monotone, Monotone.leftLim_le, Nonempty, f.hom, f.measure_Iic, f.mono, le_rfl, leftLim_le, measure_Iic, measure_sdiff, measure_singleton, nullMeasurableSet_singleton, ofReal_sub, sub_nonneg, sub_nonneg.mpr
-/
lemma measure_Iio {l : Real} (hf : Tendsto f atBot (𝓝 l)) (x : R) :
    f.measure (Iio x) = ofReal (leftLim f x - l) := by
  have : Nonempty R := ⟨x⟩
  rw [← Iic_sdiff_right]; rw [measure_sdiff _ (nullMeasurableSet_singleton x)]; rw [measure_singleton]; rw [f.measure_Iic hf]; rw [← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp

/--
theorem `measure_Ici` / 定理 `measure_Ici`

English:
theorem measure_Ici
  given: {l : Real} (hf : Tendsto f atTop (𝓝 l)) (x : R)
  proof: by
  have : Nonempty R := ⟨x⟩
  cases topOrderOrNoTopOrder R
  · have : Ici x = Icc x ⊤ := by simp
    rw [atTop_eq_pure_of_isTop isTop_top] at hf
    rw [this]; rw [measure_Icc]; rw [tendsto_nhds_unique hf (tendsto_pure_nhds f ⊤)]
  have : NoMaxOrder R := NoTopOrder.to_noMaxOrder R
  refine tendsto

中文:
定理 measure_Ici
  条件: {l : 实数} (hf : Tendsto f atTop (𝓝 l)) (x : R)
  证明: by
  have : Nonempty R := ⟨x⟩
  cases topOrderOrNoTopOrder R
  · have : Ici x = Icc x ⊤ := by simp
    rw [atTop_eq_pure_of_isTop isTop_top] at hf
    rw [this]; rw [measure_Icc]; rw [tendsto_nhds_unique hf (tendsto_pure_nhds f ⊤)]
  have : NoMaxOrder R := NoTopOrder.to_noMaxOrder R
  refine tendsto

Depends on / 依赖: ENNReal, ENNReal.tendsto_ofReal, NoMaxOrder, NoTopOrder, NoTopOrder.to_noMaxOrder, Nonempty, Tendsto, Tendsto.sub_const, atTop_eq_pure_of_isTop, isTop_top, measure_Icc, measure_Ico, simp_rw, sub_const, tendsto_leftLim_atTop_of_tendsto, tendsto_measure_Ico_atTop, tendsto_nhds_unique, tendsto_ofReal, tendsto_pure_nhds, to_noMaxOrder
-/
theorem measure_Ici {l : Real} (hf : Tendsto f atTop (𝓝 l)) (x : R) :
    f.measure (Ici x) = ofReal (l - leftLim f x) := by
  have : Nonempty R := ⟨x⟩
  cases topOrderOrNoTopOrder R
  · have : Ici x = Icc x ⊤ := by simp
    rw [atTop_eq_pure_of_isTop isTop_top] at hf
    rw [this]; rw [measure_Icc]; rw [tendsto_nhds_unique hf (tendsto_pure_nhds f ⊤)]
  have : NoMaxOrder R := NoTopOrder.to_noMaxOrder R
  refine tendsto_nhds_unique (tendsto_measure_Ico_atTop _ _) ?_
  simp_rw [measure_Ico]
  exact ENNReal.tendsto_ofReal (Tendsto.sub_const (tendsto_leftLim_atTop_of_tendsto hf) _)

/--
lemma `measure_Ioi` / 引理 `measure_Ioi`

English:
lemma measure_Ioi
  given: {l : Real} (hf : Tendsto f atTop (𝓝 l)) (x : R)
  proof: by
  rw [← Ici_sdiff_left]; rw [measure_sdiff _ (nullMeasurableSet_singleton x)]; rw [measure_singleton]; rw [f.measure_Ici hf]; rw [← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp

中文:
引理 measure_Ioi
  条件: {l : 实数} (hf : Tendsto f atTop (𝓝 l)) (x : R)
  证明: by
  rw [← Ici_sdiff_left]; rw [measure_sdiff _ (nullMeasurableSet_singleton x)]; rw [measure_singleton]; rw [f.measure_Ici hf]; rw [← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp

Depends on / 依赖: Ici_sdiff_left, Monotone, Monotone.leftLim_le, f.measure_Ici, f.mono, le_rfl, leftLim_le, measure_Ici, measure_sdiff, measure_singleton, nullMeasurableSet_singleton, ofReal_sub, sub_nonneg, sub_nonneg.mpr
-/
lemma measure_Ioi {l : Real} (hf : Tendsto f atTop (𝓝 l)) (x : R) :
    f.measure (Ioi x) = ofReal (l - f x) := by
  rw [← Ici_sdiff_left]; rw [measure_sdiff _ (nullMeasurableSet_singleton x)]; rw [measure_singleton]; rw [f.measure_Ici hf]; rw [← ofReal_sub _ (sub_nonneg.mpr <| Monotone.leftLim_le f.mono' le_rfl)]
    <;> simp

/--
lemma `measure_Ioi_of_tendsto_atTop_atTop` / 引理 `measure_Ioi_of_tendsto_atTop_atTop`

English:
lemma measure_Ioi_of_tendsto_atTop_atTop
  given: (hf : Tendsto f atTop atTop) (x : R)
  proof: by
  have : Nonempty R := ⟨x⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_atTop.mp hf (r + f x))
  exact (f.measure_Ioc x (max x N) ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
le_tsub_of_add_le_right hN _ (le_max_right x N))).

中文:
引理 measure_Ioi_of_tendsto_atTop_atTop
  条件: (hf : Tendsto f atTop atTop) (x : R)
  证明: by
  have : Nonempty R := ⟨x⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_atTop.mp hf (r + f x))
  exact (f.measure_Ioc x (max x N) ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
le_tsub_of_add_le_right hN _ (le_max_right x N))).

Depends on / 依赖: ENNReal, ENNReal.coe_nnreal_eq, ENNReal.eq_top_of_forall_nnreal_le, ENNReal.ofReal_le_ofReal, Ioc_subset_Ioi_self, Nonempty, coe_nnreal_eq, eq_top_of_forall_nnreal_le, eventually_atTop, eventually_atTop.mp, f.measure_Ioc, le_max_right, le_tsub_of_add_le_right, measure_Ioc, measure_mono, ofReal_le_ofReal, tendsto_atTop, tendsto_atTop.mp
-/
lemma measure_Ioi_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : R) :
    f.measure (Ioi x) = ∞ := by
  have : Nonempty R := ⟨x⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.mp (tendsto_atTop.mp hf (r + f x))
  exact (f.measure_Ioc x (max x N) ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
le_tsub_of_add_le_right hN _ (le_max_right x N))).trans (measure_mono Ioc_subset_Ioi_self)

/--
lemma `measure_Ici_of_tendsto_atTop_atTop` / 引理 `measure_Ici_of_tendsto_atTop_atTop`

English:
lemma measure_Ici_of_tendsto_atTop_atTop
  given: (hf : Tendsto f atTop atTop) (x : R)
  proof: by
  rw [← top_le_iff]; rw [← f.measure_Ioi_of_tendsto_atTop_atTop hf x]
  exact measure_mono Ioi_subset_Ici_self

中文:
引理 measure_Ici_of_tendsto_atTop_atTop
  条件: (hf : Tendsto f atTop atTop) (x : R)
  证明: by
  rw [← top_le_iff]; rw [← f.measure_Ioi_of_tendsto_atTop_atTop hf x]
  exact measure_mono Ioi_subset_Ici_self

Depends on / 依赖: Ioi_subset_Ici_self, f.measure_Ioi_of_tendsto_atTop_atTop, measure_Ioi_of_tendsto_atTop_atTop, measure_mono, top_le_iff
-/
lemma measure_Ici_of_tendsto_atTop_atTop (hf : Tendsto f atTop atTop) (x : R) :
    f.measure (Ici x) = ∞ := by
  rw [← top_le_iff]; rw [← f.measure_Ioi_of_tendsto_atTop_atTop hf x]
  exact measure_mono Ioi_subset_Ici_self

/--
lemma `measure_Iic_of_tendsto_atBot_atBot` / 引理 `measure_Iic_of_tendsto_atBot_atBot`

English:
lemma measure_Iic_of_tendsto_atBot_atBot
  given: (hf : Tendsto f atBot atBot) (x : R)
  proof: by
  have : Nonempty R := ⟨x⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨N, hN⟩ := eventually_atBot.mp (tendsto_atBot.mp hf (f x - r))
  exact (f.measure_Ioc (min x N) x ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
le_sub_comm.mp hN _ (min_le_right x N))).trans (me

中文:
引理 measure_Iic_of_tendsto_atBot_atBot
  条件: (hf : Tendsto f atBot atBot) (x : R)
  证明: by
  have : Nonempty R := ⟨x⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨N, hN⟩ := eventually_atBot.mp (tendsto_atBot.mp hf (f x - r))
  exact (f.measure_Ioc (min x N) x ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
le_sub_comm.mp hN _ (min_le_right x N))).trans (me

Depends on / 依赖: ENNReal, ENNReal.coe_nnreal_eq, ENNReal.eq_top_of_forall_nnreal_le, ENNReal.ofReal_le_ofReal, Ioc_subset_Iic_self, Nonempty, coe_nnreal_eq, eq_top_of_forall_nnreal_le, eventually_atBot, eventually_atBot.mp, f.measure_Ioc, le_sub_comm, le_sub_comm.mp, measure_Ioc, measure_mono, min_le_right, ofReal_le_ofReal, tendsto_atBot, tendsto_atBot.mp
-/
lemma measure_Iic_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : R) :
    f.measure (Iic x) = ∞ := by
  have : Nonempty R := ⟨x⟩
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  obtain ⟨N, hN⟩ := eventually_atBot.mp (tendsto_atBot.mp hf (f x - r))
  exact (f.measure_Ioc (min x N) x ▸ ENNReal.coe_nnreal_eq r ▸ (ENNReal.ofReal_le_ofReal <|
le_sub_comm.mp hN _ (min_le_right x N))).trans (measure_mono Ioc_subset_Iic_self)

/--
lemma `measure_Iio_of_tendsto_atBot_atBot` / 引理 `measure_Iio_of_tendsto_atBot_atBot`

English:
lemma measure_Iio_of_tendsto_atBot_atBot
  given: (hf : Tendsto f atBot atBot) (x : R)
  proof: by
  have : Nonempty R := ⟨x⟩
  cases botOrderOrNoBotOrder R
  · rw [atBot_eq_pure_of_isBot isBot_bot] at hf
    simpa using (tendsto_pure_left.1 hf) _ (Iio_mem_atBot (f ⊥))
  have : NoMinOrder R := NoBotOrder.to_noMinOrder R
  obtain ⟨y, hy⟩ : exists y, y < x := exists_lt x
  rw [← top_le_iff]; rw 

中文:
引理 measure_Iio_of_tendsto_atBot_atBot
  条件: (hf : Tendsto f atBot atBot) (x : R)
  证明: by
  have : Nonempty R := ⟨x⟩
  cases botOrderOrNoBotOrder R
  · rw [atBot_eq_pure_of_isBot isBot_bot] at hf
    simpa using (tendsto_pure_left.1 hf) _ (Iio_mem_atBot (f ⊥))
  have : NoMinOrder R := NoBotOrder.to_noMinOrder R
  obtain ⟨y, hy⟩ : exists y, y < x := exists_lt x
  rw [← top_le_iff]; rw 

Depends on / 依赖: Iic_subset_Iio, Iio_mem_atBot, NoBotOrder, NoBotOrder.to_noMinOrder, NoMinOrder, Nonempty, Set.Iic_subset_Iio.mpr, atBot_eq_pure_of_isBot, botOrderOrNoBotOrder, exists_lt, f.measure_Iic_of_tendsto_atBot_atBot, isBot_bot, measure_Iic_of_tendsto_atBot_atBot, measure_mono, tendsto_pure_left, to_noMinOrder, top_le_iff
-/
lemma measure_Iio_of_tendsto_atBot_atBot (hf : Tendsto f atBot atBot) (x : R) :
    f.measure (Iio x) = ∞ := by
  have : Nonempty R := ⟨x⟩
  cases botOrderOrNoBotOrder R
  · rw [atBot_eq_pure_of_isBot isBot_bot] at hf
    simpa using (tendsto_pure_left.1 hf) _ (Iio_mem_atBot (f ⊥))
  have : NoMinOrder R := NoBotOrder.to_noMinOrder R
  obtain ⟨y, hy⟩ : exists y, y < x := exists_lt x
  rw [← top_le_iff]; rw [← f.measure_Iic_of_tendsto_atBot_atBot hf y]
exact measure_mono Set.Iic_subset_Iio.mpr hy

/--
theorem `measure_univ` / 定理 `measure_univ`

English:
theorem measure_univ
  statement: [Nonempty R]
  proof: by
  refine tendsto_nhds_unique (tendsto_measure_Iic_atTop _) ?_
  simp_rw [measure_Iic f hfl]
  exact ENNReal.tendsto_ofReal (Tendsto.sub_const hfu _)

中文:
定理 measure_univ
  结论: [Nonempty R]
  证明: by
  refine tendsto_nhds_unique (tendsto_measure_Iic_atTop _) ?_
  simp_rw [measure_Iic f hfl]
  exact ENNReal.tendsto_ofReal (Tendsto.sub_const hfu _)

Depends on / 依赖: ENNReal, ENNReal.tendsto_ofReal, Tendsto, Tendsto.sub_const, measure_Iic, simp_rw, sub_const, tendsto_measure_Iic_atTop, tendsto_nhds_unique, tendsto_ofReal
-/
theorem measure_univ [Nonempty R]
    {l u : Real} (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    f.measure univ = ofReal (u - l) := by
  refine tendsto_nhds_unique (tendsto_measure_Iic_atTop _) ?_
  simp_rw [measure_Iic f hfl]
  exact ENNReal.tendsto_ofReal (Tendsto.sub_const hfu _)

/--
lemma `measure_univ_of_tendsto_atTop_atTop` / 引理 `measure_univ_of_tendsto_atTop_atTop`

English:
lemma measure_univ_of_tendsto_atTop_atTop
  given: [Nonempty R] (hf : Tendsto f atTop atTop)
  proof: by
  inhabit R
  rw [← top_le_iff]; rw [← f.measure_Ioi_of_tendsto_atTop_atTop hf default]
  exact measure_mono (subset_univ _)

中文:
引理 measure_univ_of_tendsto_atTop_atTop
  条件: [Nonempty R] (hf : Tendsto f atTop atTop)
  证明: by
  inhabit R
  rw [← top_le_iff]; rw [← f.measure_Ioi_of_tendsto_atTop_atTop hf default]
  exact measure_mono (subset_univ _)

Depends on / 依赖: f.measure_Ioi_of_tendsto_atTop_atTop, inhabit, measure_Ioi_of_tendsto_atTop_atTop, measure_mono, subset_univ, top_le_iff
-/
lemma measure_univ_of_tendsto_atTop_atTop [Nonempty R] (hf : Tendsto f atTop atTop) :
    f.measure univ = ∞ := by
  inhabit R
  rw [← top_le_iff]; rw [← f.measure_Ioi_of_tendsto_atTop_atTop hf default]
  exact measure_mono (subset_univ _)

/--
lemma `measure_univ_of_tendsto_atBot_atBot` / 引理 `measure_univ_of_tendsto_atBot_atBot`

English:
lemma measure_univ_of_tendsto_atBot_atBot
  given: [Nonempty R] (hf : Tendsto f atBot atBot)
  proof: by
  inhabit R
  rw [← top_le_iff]; rw [← f.measure_Iio_of_tendsto_atBot_atBot hf default]
  exact measure_mono (subset_univ _)

中文:
引理 measure_univ_of_tendsto_atBot_atBot
  条件: [Nonempty R] (hf : Tendsto f atBot atBot)
  证明: by
  inhabit R
  rw [← top_le_iff]; rw [← f.measure_Iio_of_tendsto_atBot_atBot hf default]
  exact measure_mono (subset_univ _)

Depends on / 依赖: f.measure_Iio_of_tendsto_atBot_atBot, inhabit, measure_Iio_of_tendsto_atBot_atBot, measure_mono, subset_univ, top_le_iff
-/
lemma measure_univ_of_tendsto_atBot_atBot [Nonempty R] (hf : Tendsto f atBot atBot) :
    f.measure univ = ∞ := by
  inhabit R
  rw [← top_le_iff]; rw [← f.measure_Iio_of_tendsto_atBot_atBot hf default]
  exact measure_mono (subset_univ _)

/--
lemma `isFiniteMeasure` / 引理 `isFiniteMeasure`

English:
lemma isFiniteMeasure
  statement: {l u : Real}
  proof: by
  constructor
  cases isEmpty_or_nonempty R
  · simp [eq_empty_of_isEmpty]
  · simp [f.measure_univ hfl hfu]

中文:
引理 isFiniteMeasure
  结论: {l u : 实数}
  证明: by
  constructor
  cases isEmpty_or_nonempty R
  · simp [eq_empty_of_isEmpty]
  · simp [f.measure_univ hfl hfu]

Depends on / 依赖: eq_empty_of_isEmpty, f.measure_univ, isEmpty_or_nonempty, measure_univ
-/
lemma isFiniteMeasure {l u : Real}
    (hfl : Tendsto f atBot (𝓝 l)) (hfu : Tendsto f atTop (𝓝 u)) :
    IsFiniteMeasure f.measure := by
  constructor
  cases isEmpty_or_nonempty R
  · simp [eq_empty_of_isEmpty]
  · simp [f.measure_univ hfl hfu]

/--
lemma `isFiniteMeasure_of_forall_abs_le` / 引理 `isFiniteMeasure_of_forall_abs_le`

English:
lemma isFiniteMeasure_of_forall_abs_le
  given: {C : Real} (h : forall x, |f x| <= C)
  proof: by
  cases isEmpty_or_nonempty R
  · infer_instance
  obtain ⟨u, hu⟩ : exists u, Tendsto f atTop (𝓝 u) := by
    rcases tendsto_atTop_of_monotone f.mono with H | H
    · obtain ⟨x, hx⟩ : exists x, C + 1 <= f x := (tendsto_atTop.1 H (C + 1)).exists
      grind
    exact H
  obtain ⟨l, hl⟩ : exists l,

中文:
引理 isFiniteMeasure_of_forall_abs_le
  条件: {C : 实数} (h : 对任意 x, |f x| <= C)
  证明: by
  cases isEmpty_or_nonempty R
  · infer_instance
  obtain ⟨u, hu⟩ : exists u, Tendsto f atTop (𝓝 u) := by
    rcases tendsto_atTop_of_monotone f.mono with H | H
    · obtain ⟨x, hx⟩ : exists x, C + 1 <= f x := (tendsto_atTop.1 H (C + 1)).exists
      grind
    exact H
  obtain ⟨l, hl⟩ : exists l,

Depends on / 依赖: Tendsto, f.isFiniteMeasure, f.mono, infer_instance, isEmpty_or_nonempty, isFiniteMeasure, tendsto_atBot, tendsto_atBot_of_monotone, tendsto_atTop, tendsto_atTop_of_monotone
-/
lemma isFiniteMeasure_of_forall_abs_le {C : Real} (h : forall x, |f x| <= C) :
    IsFiniteMeasure f.measure := by
  cases isEmpty_or_nonempty R
  · infer_instance
  obtain ⟨u, hu⟩ : exists u, Tendsto f atTop (𝓝 u) := by
    rcases tendsto_atTop_of_monotone f.mono with H | H
    · obtain ⟨x, hx⟩ : exists x, C + 1 <= f x := (tendsto_atTop.1 H (C + 1)).exists
      grind
    exact H
  obtain ⟨l, hl⟩ : exists l, Tendsto f atBot (𝓝 l) := by
    rcases tendsto_atBot_of_monotone f.mono with H | H
    · obtain ⟨x, hx⟩ : exists x, f x <= - C - 1 := (tendsto_atBot.1 H (-C - 1)).exists
      grind
    exact H
  exact f.isFiniteMeasure hl hu

/--
lemma `isProbabilityMeasure` / 引理 `isProbabilityMeasure`

English:
lemma isProbabilityMeasure
  statement: [Nonempty R]
  proof: ⟨by simp [f.measure_univ hf_bot hf_top]⟩

中文:
引理 isProbabilityMeasure
  结论: [Nonempty R]
  证明: ⟨by simp [f.measure_univ hf_bot hf_top]⟩

Depends on / 依赖: f.measure_univ, hf_bot, hf_top, measure_univ
-/
lemma isProbabilityMeasure [Nonempty R]
    (hf_bot : Tendsto f atBot (𝓝 0)) (hf_top : Tendsto f atTop (𝓝 1)) :
    IsProbabilityMeasure f.measure := ⟨by simp [f.measure_univ hf_bot hf_top]⟩

/--
Instance `instIsLocallyFiniteMeasure` / 实例 `instIsLocallyFiniteMeasure`

English:
instance instIsLocallyFiniteMeasure
  signature: : IsLocallyFiniteMeasure f.measure
  body: by
  refine ⟨fun x => ?_⟩
  obtain ⟨b, c, -, h, -⟩ : exists b c, x in Icc b c ∧ Icc b c in 𝓝 x ∧ Icc b c subseteq univ :=
    exists_Icc_mem_subset_of_mem_nhds (by simp)
  exact ⟨Icc b c, h, by simp⟩

中文:
实例 instIsLocallyFiniteMeasure
  签名: : IsLocallyFiniteMeasure f.measure
  定义体: by
  refine ⟨fun x => ?_⟩
  obtain ⟨b, c, -, h, -⟩ : exists b c, x in Icc b c ∧ Icc b c in 𝓝 x ∧ Icc b c subseteq univ :=
    exists_Icc_mem_subset_of_mem_nhds (by simp)
  exact ⟨Icc b c, h, by simp⟩

Depends on / 依赖: exists_Icc_mem_subset_of_mem_nhds, subseteq
-/
instance instIsLocallyFiniteMeasure : IsLocallyFiniteMeasure f.measure := by
  refine ⟨fun x => ?_⟩
  obtain ⟨b, c, -, h, -⟩ : exists b c, x in Icc b c ∧ Icc b c in 𝓝 x ∧ Icc b c subseteq univ :=
    exists_Icc_mem_subset_of_mem_nhds (by simp)
  exact ⟨Icc b c, h, by simp⟩

/--
lemma `eq_of_measure_of_tendsto_atBot` / 引理 `eq_of_measure_of_tendsto_atBot`

English:
lemma eq_of_measure_of_tendsto_atBot
  statement: (g : StieltjesFunction R) {l : Real}
  proof: by
  ext x
  have hf := measure_Iic f hfl x
  rw [hfg]; rw [measure_Iic g hgl x]; rw [ENNReal.ofReal_eq_ofReal_iff]; rw [eq_comm] at hf
  · simpa using hf
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto g.mono hgl x
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto f.mono hfl x

中文:
引理 eq_of_measure_of_tendsto_atBot
  结论: (g : StieltjesFunction R) {l : 实数}
  证明: by
  ext x
  have hf := measure_Iic f hfl x
  rw [hfg]; rw [measure_Iic g hgl x]; rw [ENNReal.ofReal_eq_ofReal_iff]; rw [eq_comm] at hf
  · simpa using hf
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto g.mono hgl x
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto f.mono hfl x

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_ofReal_iff, Monotone, Monotone.le_of_tendsto, eq_comm, f.mono, g.mono, le_of_tendsto, measure_Iic, ofReal_eq_ofReal_iff, sub_nonneg
-/
lemma eq_of_measure_of_tendsto_atBot (g : StieltjesFunction R) {l : Real}
    (hfg : f.measure = g.measure) (hfl : Tendsto f atBot (𝓝 l)) (hgl : Tendsto g atBot (𝓝 l)) :
    f = g := by
  ext x
  have hf := measure_Iic f hfl x
  rw [hfg]; rw [measure_Iic g hgl x]; rw [ENNReal.ofReal_eq_ofReal_iff]; rw [eq_comm] at hf
  · simpa using hf
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto g.mono hgl x
  · rw [sub_nonneg]
    exact Monotone.le_of_tendsto f.mono hfl x

/--
lemma `eq_of_measure_of_eq` / 引理 `eq_of_measure_of_eq`

English:
lemma eq_of_measure_of_eq
  statement: (g : StieltjesFunction R) {y : R}
  proof: by
  ext x
  cases le_total x y with
  | inl hxy =>
    have hf := measure_Ioc f x y
    rw [hfg]; rw [measure_Ioc g x y]; rw [ENNReal.ofReal_eq_ofReal_iff]; rw [eq_comm]; rw [hy] at hf
    · simpa using hf
    · rw [sub_nonneg]
      exact g.mono hxy
    · rw [sub_nonneg]
      exact f.mono hxy
  |

中文:
引理 eq_of_measure_of_eq
  结论: (g : StieltjesFunction R) {y : R}
  证明: by
  ext x
  cases le_total x y with
  | inl hxy =>
    have hf := measure_Ioc f x y
    rw [hfg]; rw [measure_Ioc g x y]; rw [ENNReal.ofReal_eq_ofReal_iff]; rw [eq_comm]; rw [hy] at hf
    · simpa using hf
    · rw [sub_nonneg]
      exact g.mono hxy
    · rw [sub_nonneg]
      exact f.mono hxy
  |

Depends on / 依赖: ENNReal, ENNReal.ofReal_eq_ofReal_iff, eq_comm, f.mono, g.mono, le_total, measure_Ioc, ofReal_eq_ofReal_iff, sub_nonneg
-/
lemma eq_of_measure_of_eq (g : StieltjesFunction R) {y : R}
    (hfg : f.measure = g.measure) (hy : f y = g y) :
    f = g := by
  ext x
  cases le_total x y with
  | inl hxy =>
    have hf := measure_Ioc f x y
    rw [hfg]; rw [measure_Ioc g x y]; rw [ENNReal.ofReal_eq_ofReal_iff]; rw [eq_comm]; rw [hy] at hf
    · simpa using hf
    · rw [sub_nonneg]
      exact g.mono hxy
    · rw [sub_nonneg]
      exact f.mono hxy
  | inr hxy =>
    have hf := measure_Ioc f y x
    rw [hfg]; rw [measure_Ioc g y x]; rw [ENNReal.ofReal_eq_ofReal_iff]; rw [eq_comm]; rw [hy] at hf
    · simpa using hf
    · rw [sub_nonneg]
      exact g.mono hxy
    · rw [sub_nonneg]
      exact f.mono hxy

@[simp]
/--
lemma `measure_const` / 引理 `measure_const`

English:
lemma measure_const
  given: (c : Real)
  statement: (StieltjesFunction.const R c).measure = 0
  proof: by
  apply Measure.ext_of_Icc _ _ (fun a b hab => ?_)
  simp only [measure_Icc, const_apply, Measure.coe_zero, Pi.ofNat_apply, ofReal_eq_zero,
    tsub_le_iff_right, zero_add]
  rw [ContinuousWithinAt.leftLim_eq]
  · simp
  · exact continuousWithinAt_const

@[simp]

中文:
引理 measure_const
  条件: (c : 实数)
  结论: (StieltjesFunction.const R c).measure = 0
  证明: by
  apply Measure.ext_of_Icc _ _ (fun a b hab => ?_)
  simp only [measure_Icc, const_apply, Measure.coe_zero, Pi.ofNat_apply, ofReal_eq_zero,
    tsub_le_iff_right, zero_add]
  rw [ContinuousWithinAt.leftLim_eq]
  · simp
  · exact continuousWithinAt_const

@[simp]

Depends on / 依赖: ContinuousWithinAt, ContinuousWithinAt.leftLim_eq, Measure, Measure.coe_zero, Measure.ext_of_Icc, Pi.ofNat_apply, coe_zero, const_apply, continuousWithinAt_const, ext_of_Icc, leftLim_eq, measure_Icc, ofNat_apply, ofReal_eq_zero, tsub_le_iff_right, zero_add
-/
lemma measure_const (c : Real) : (StieltjesFunction.const R c).measure = 0 := by
  apply Measure.ext_of_Icc _ _ (fun a b hab => ?_)
  simp only [measure_Icc, const_apply, Measure.coe_zero, Pi.ofNat_apply, ofReal_eq_zero,
    tsub_le_iff_right, zero_add]
  rw [ContinuousWithinAt.leftLim_eq]
  · simp
  · exact continuousWithinAt_const

@[simp]
/--
lemma `measure_zero` / 引理 `measure_zero`

English:
lemma measure_zero
  statement: (0 : StieltjesFunction R).measure = 0
  proof: measure_const 0

@[simp]

中文:
引理 measure_zero
  结论: (0 : StieltjesFunction R).measure = 0
  证明: measure_const 0

@[simp]

Depends on / 依赖: measure_const
-/
lemma measure_zero : (0 : StieltjesFunction R).measure = 0 := measure_const 0

@[simp]
/--
lemma `measure_add` / 引理 `measure_add`

English:
lemma measure_add
  given: (f g : StieltjesFunction R)
  statement: (f + g).measure = f.measure + g.measure
  proof: by
  refine Measure.ext_of_Icc _ _ (fun a b h => ?_)
  have : leftLim (f + g) a = leftLim f a + leftLim g a := by
    rcases Filter.eq_or_neBot (𝓝[<] a) with ha | ha
    · simp [leftLim_eq_of_eq_bot _ ha]
    · exact tendsto_nhds_unique ((f + g).mono.tendsto_leftLim a)
        ((f.mono.tendsto_leftL

中文:
引理 measure_add
  条件: (f g : StieltjesFunction R)
  结论: (f + g).measure = f.measure + g.measure
  证明: by
  refine Measure.ext_of_Icc _ _ (fun a b h => ?_)
  have : leftLim (f + g) a = leftLim f a + leftLim g a := by
    rcases Filter.eq_or_neBot (𝓝[<] a) with ha | ha
    · simp [leftLim_eq_of_eq_bot _ ha]
    · exact tendsto_nhds_unique ((f + g).mono.tendsto_leftLim a)
        ((f.mono.tendsto_leftL

Depends on / 依赖: ENNReal, ENNReal.ofReal_add, Filter, Filter.eq_or_neBot, Measure, Measure.coe_add, Measure.ext_of_Icc, Pi.add_apply, add_apply, coe_add, eq_or_neBot, ext_of_Icc, f.mono.leftLim_le, f.mono.tendsto_leftLim, g.mono.leftLim_le, g.mono.tendsto_leftLim, leftLim, leftLim_eq_of_eq_bot, leftLim_le, measure_Icc
-/
lemma measure_add (f g : StieltjesFunction R) : (f + g).measure = f.measure + g.measure := by
  refine Measure.ext_of_Icc _ _ (fun a b h => ?_)
  have : leftLim (f + g) a = leftLim f a + leftLim g a := by
    rcases Filter.eq_or_neBot (𝓝[<] a) with ha | ha
    · simp [leftLim_eq_of_eq_bot _ ha]
    · exact tendsto_nhds_unique ((f + g).mono.tendsto_leftLim a)
        ((f.mono.tendsto_leftLim a).add (g.mono.tendsto_leftLim a))
  simp only [measure_Icc, add_apply, Measure.coe_add, Pi.add_apply, this]
  rw [← ENNReal.ofReal_add (sub_nonneg_of_le (f.mono.leftLim_le h))
    (sub_nonneg_of_le (g.mono.leftLim_le h))]
  ring_nf

@[simp]
/--
lemma `measure_smul` / 引理 `measure_smul`

English:
lemma measure_smul
  given: (c : Real>=0) (f : StieltjesFunction R)
  statement: (c • f).measure = c • f.measure
  proof: by
  refine Measure.ext_of_Icc _ _ (fun a b h => ?_)
  simp only [measure_Icc, Measure.smul_apply]
  change ofReal (c * f b - leftLim (c • f) a) = c • ofReal (f b - leftLim f a)
  have : leftLim (c • f) a = c * leftLim f a := by
    rcases Filter.eq_or_neBot (𝓝[<] a) with ha | ha
    · simp [leftLim

中文:
引理 measure_smul
  条件: (c : 实数>=0) (f : StieltjesFunction R)
  结论: (c • f).measure = c • f.measure
  证明: by
  refine Measure.ext_of_Icc _ _ (fun a b h => ?_)
  simp only [measure_Icc, Measure.smul_apply]
  change ofReal (c * f b - leftLim (c • f) a) = c • ofReal (f b - leftLim f a)
  have : leftLim (c • f) a = c * leftLim f a := by
    rcases Filter.eq_or_neBot (𝓝[<] a) with ha | ha
    · simp [leftLim

Depends on / 依赖: ENNReal, ENNReal.ofReal_mul, Filter, Filter.eq_or_neBot, Measure, Measure.ext_of_Icc, Measure.smul_apply, _root_, _root_.mul_sub, const_smul, eq_or_neBot, ext_of_Icc, f.mono.tendsto_leftLim, leftLim, leftLim_eq_of_eq_bot, measure_Icc, mono.tendsto_leftLim, mul_sub, ofReal, ofReal_coe_nnr
-/
lemma measure_smul (c : Real>=0) (f : StieltjesFunction R) : (c • f).measure = c • f.measure := by
  refine Measure.ext_of_Icc _ _ (fun a b h => ?_)
  simp only [measure_Icc, Measure.smul_apply]
  change ofReal (c * f b - leftLim (c • f) a) = c • ofReal (f b - leftLim f a)
  have : leftLim (c • f) a = c * leftLim f a := by
    rcases Filter.eq_or_neBot (𝓝[<] a) with ha | ha
    · simp [leftLim_eq_of_eq_bot _ ha]
      rfl
    · exact tendsto_nhds_unique ((c • f).mono.tendsto_leftLim a)
        ((f.mono.tendsto_leftLim a).const_smul c)
  rw [this]; rw [← _root_.mul_sub]; rw [ENNReal.ofReal_mul zero_le_coe]; rw [ofReal_coe_nnreal]; rw [← smul_eq_mul]
  rfl

end StieltjesFunction
