/-
Copyright (c) 2024 Josha Dekker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josha Dekker
-/
module

public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Filter.Finite
public import Mathlib.Order.Filter.CountableInter
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Tactic.NormNum

/-!
# Filters with a cardinal intersection property

In this file we define `CardinalInterFilter l c` to be the class of filters with the following
property: for any collection of sets `s ∈ l` with cardinality strictly less than `c`,
their intersection belongs to `l` as well.

## Main results
* `Filter.cardinalInterFilter_aleph0` establishes that every filter `l` is a
    `CardinalInterFilter l ℵ₀`
* `CardinalInterFilter.toCountableInterFilter` establishes that every `CardinalInterFilter l c` with
    `c > ℵ₀` is a `CountableInterFilter`.
* `CountableInterFilter.toCardinalInterFilter` establishes that every `CountableInterFilter l` is a
    `CardinalInterFilter l ℵ₁`.
* `CardinalInterFilter.of_cardinalInterFilter_of_lt` establishes that we have
  `CardinalInterFilter l c` → `CardinalInterFilter l a` for all `a < c`.

## Tags
filter, cardinal
-/

@[expose] public section


open Set Filter Cardinal

universe u
variable {ι : Type u} {α β : Type u} {c : Cardinal.{u}}

/-- A filter `l` has the cardinal `c` intersection property if for any collection
of less than `c` sets `s ∈ l`, their intersection belongs to `l` as well. -/
/-
**CardinalInterFilter** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u} → Filter α → Cardinal.{u} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filter `l` has the cardinal `c` intersection property if for any collection
of less than `c` sets `s ∈ l`, their intersection belongs to `l` as well.
-/
class CardinalInterFilter (l : Filter α) (c : Cardinal.{u}) : Prop where
  /-- For a collection of sets `s ∈ l` with cardinality below c,
  their intersection belongs to `l` as well. -/
  cardinal_sInter_mem : ∀ S : Set (Set α), (#S < c) → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l

variable {l : Filter α}
/-
**cardinal_sInter_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardinal_sInter_mem {S : Set (Set α)} [CardinalInterFilter l c] (hSc : #S 
< c) : ⋂₀ S in l ↔ forall s in S, s in l
参数：Set α；hSc : #S < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `CardinalInterFilter.cardinal_sInter_mem`：∀ {α : Type u} {l : Filter α} {
c : Cardinal.{u}} [self : CardinalInterFilter l c] (S : Set (Set α)),   Cardinal
.mk ↑S < c → (∀ s ∈ S, s ∈ l)…
-/
theorem cardinal_sInter_mem {S : Set (Set α)} [CardinalInterFilter l c] (hSc : #S < c) :
    ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l := ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
  CardinalInterFilter.cardinal_sInter_mem _ hSc⟩

/-- Every filter is a CardinalInterFilter with c = ℵ₀ -/
/-
**_root_.Filter.cardinalInterFilter_aleph0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.Filter.cardinalInterFilter_aleph0 (l : Filter α) : CardinalInterFil
ter l ℵ₀ where cardinal_sInter_mem
参数：l : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every filter is a CardinalInterFilter with c = ℵ₀
-/
theorem _root_.Filter.cardinalInterFilter_aleph0 (l : Filter α) : CardinalInterFilter l ℵ₀ where
  cardinal_sInter_mem := by
    simp_all only [lt_aleph0_iff_subtype_finite, ofPred_mem_eq, sInter_mem,
      implies_true]

/-- Every CardinalInterFilter with c > ℵ₀ is a CountableInterFilter -/
/-
**CardinalInterFilter.toCountableInterFilter** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CardinalInterFilter.toCountableInterFilter (l : Filter α) [CardinalInterFi
lter l c] (hc : ℵ₀ < c) : CountableInterFilter l where countable_sInter_mem S hS
 a
参数：l : Filter α；hc : ℵ₀ < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CardinalInterFilter.cardinal_sInter_mem`：∀ {α : Type u} {l : Filter α} {
c : Cardinal.{u}} [self : CardinalInterFilter l c] (S : Set (Set α)),   Cardinal
.mk ↑S < c → (∀ s ∈ S, s ∈ l)…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Set.Countable.le_aleph0`：∀ {α : Type u} {s : Set α}, s.Countable → Cardi
nal.mk ↑s ≤ Cardinal.aleph0

--- 原说明 ---
Every CardinalInterFilter with c > ℵ₀ is a CountableInterFilter
-/
theorem CardinalInterFilter.toCountableInterFilter (l : Filter α) [CardinalInterFilter l c]
    (hc : ℵ₀ < c) : CountableInterFilter l where
  countable_sInter_mem S hS a :=
    CardinalInterFilter.cardinal_sInter_mem S (lt_of_le_of_lt (Set.Countable.le_aleph0 hS) hc) a

/-- Every CountableInterFilter is a CardinalInterFilter with c = ℵ₁ -/
/-
**CountableInterFilter.toCardinalInterFilter** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CountableInterFilter.toCardinalInterFilter (l : Filter α) [CountableInterF
ilter l] : CardinalInterFilter l ℵ₁ where cardinal_sInter_mem S hS a
参数：l : Filter α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CountableInterFilter.countable_sInter_mem`：∀ {α : Type u_2} {l : Filter 
α} [self : CountableInterFilter l] (S : Set (Set α)),   S.Countable → (∀ s ∈ S, 
s ∈ l) → ⋂₀ S ∈ l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
· 使用定理 `Cardinal.lt_aleph_one_iff`：lt_aleph_one_iff {c : Cardinal} : c < ℵ₁ ↔ c 
<= ℵ₀

--- 原说明 ---
Every CountableInterFilter is a CardinalInterFilter with c = ℵ₁
-/
instance CountableInterFilter.toCardinalInterFilter (l : Filter α) [CountableInterFilter l] :
    CardinalInterFilter l ℵ₁ where
  cardinal_sInter_mem S hS a := by
    apply CountableInterFilter.countable_sInter_mem S _ a
    rwa [← le_aleph0_iff_set_countable, ← lt_aleph_one_iff]
/-
**cardinalInterFilter_aleph_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardinalInterFilter_aleph_one_iff : CardinalInterFilter l ℵ₁ ↔ CountableIn
terFilter l where mpr _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CardinalInterFilter.cardinal_sInter_mem`：∀ {α : Type u} {l : Filter α} {
c : Cardinal.{u}} [self : CardinalInterFilter l c] (S : Set (Set α)),   Cardinal
.mk ↑S < c → (∀ s ∈ S, s ∈ l)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lt_aleph_one_iff`：lt_aleph_one_iff {c : Cardinal} : c < ℵ₁ ↔ c 
<= ℵ₀
· 使用定理 `Cardinal.le_aleph0_iff_set_countable`：le_aleph0_iff_set_countable {s : S
et α} : #s <= ℵ₀ ↔ s.Countable
-/
theorem cardinalInterFilter_aleph_one_iff : CardinalInterFilter l ℵ₁ ↔ CountableInterFilter l where
  mpr _ := CountableInterFilter.toCardinalInterFilter l
  mp _ := by
    refine ⟨fun S h a ↦ CardinalInterFilter.cardinal_sInter_mem (c := ℵ₁) S ?_ a⟩
    rwa [lt_aleph_one_iff, le_aleph0_iff_set_countable]

/-- Every `CardinalInterFilter` for some `c` also is a `CardinalInterFilter` for any `a ≤ c`. -/
/-
**CardinalInterFilter.of_cardinalInterFilter_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CardinalInterFilter.of_cardinalInterFilter_of_le (l : Filter α) [CardinalI
nterFilter l c] {a : Cardinal.{u}} (hac : a <= c) : CardinalInterFilter l a wher
e cardinal_sInter_mem S hS a
参数：l : Filter α；hac : a <= c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CardinalInterFilter.cardinal_sInter_mem`：∀ {α : Type u} {l : Filter α} {
c : Cardinal.{u}} [self : CardinalInterFilter l c] (S : Set (Set α)),   Cardinal
.mk ↑S < c → (∀ s ∈ S, s ∈ l)…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c

--- 原说明 ---
Every `CardinalInterFilter` for some `c` also is a `CardinalInterFilter` for any
 `a ≤ c`.
-/
theorem CardinalInterFilter.of_cardinalInterFilter_of_le (l : Filter α) [CardinalInterFilter l c]
    {a : Cardinal.{u}} (hac : a ≤ c) :
    CardinalInterFilter l a where
  cardinal_sInter_mem S hS a :=
    CardinalInterFilter.cardinal_sInter_mem S (lt_of_lt_of_le hS hac) a
/-
**CardinalInterFilter.of_cardinalInterFilter_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CardinalInterFilter.of_cardinalInterFilter_of_lt (l : Filter α) [CardinalI
nterFilter l c] {a : Cardinal.{u}} (hac : a < c) : CardinalInterFilter l a
参数：l : Filter α；hac : a < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CardinalInterFilter.of_cardinalInterFilter_of_le`：CardinalInterFilter.of
_cardinalInterFilter_of_le (l : Filter α) [CardinalInterFilter l c] {a : Cardina
l.{u}} (hac : a <= c) : CardinalInterF…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem CardinalInterFilter.of_cardinalInterFilter_of_lt (l : Filter α) [CardinalInterFilter l c]
    {a : Cardinal.{u}} (hac : a < c) : CardinalInterFilter l a :=
  CardinalInterFilter.of_cardinalInterFilter_of_le l (hac.le)

namespace Filter

variable [CardinalInterFilter l c]

/-
**Filter.cardinal_iInter_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：cardinal_iInter_mem {s : ι -> Set α} (hic : #ι < c) : (⋂ i, s i) in l ↔ fo
rall i, s i in l
参数：hic : #ι < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `cardinal_sInter_mem`：cardinal_sInter_mem {S : Set (Set α)} [CardinalInte
rFilter l c] (hSc : #S < c) : ⋂₀ S in l ↔ forall s in S, s in l
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Cardinal.mk_range_le`：mk_range_le {α β : Type u} {f : α -> β} : #(range 
f) <= #α
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem cardinal_iInter_mem {s : ι → Set α} (hic : #ι < c) :
    (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l := by
  rw [← sInter_range _]
  apply (cardinal_sInter_mem (lt_of_le_of_lt Cardinal.mk_range_le hic)).trans
  exact forall_mem_range
/-
**Filter.cardinal_bInter_mem** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：cardinal_bInter_mem {S : Set ι} (hS : #S < c) {s : forall i in S, Set α} :
 (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ forall i, forall hi : i in S, s i ‹_› in l
参数：hS : #S < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.cardinal_iInter_mem`：cardinal_iInter_mem {s : ι -> Set α} (hic : 
#ι < c) : (⋂ i, s i) in l ↔ forall i, s i in l
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem cardinal_bInter_mem {S : Set ι} (hS : #S < c)
    {s : ∀ i ∈ S, Set α} :
    (⋂ i, ⋂ hi : i ∈ S, s i ‹_›) ∈ l ↔ ∀ i, ∀ hi : i ∈ S, s i ‹_› ∈ l := by
  rw [biInter_eq_iInter]
  exact (cardinal_iInter_mem hS).trans Subtype.forall
/-
**Filter.eventually_cardinal_forall** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_cardinal_forall {p : α -> ι -> Prop} (hic : #ι < c) : (forallᶠ 
x in l, forall i, p x i) ↔ forall i, forallᶠ x in l, p x i
参数：hic : #ι < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `Filter.cardinal_iInter_mem`：cardinal_iInter_mem {s : ι -> Set α} (hic : 
#ι < c) : (⋂ i, s i) in l ↔ forall i, s i in l
-/
theorem eventually_cardinal_forall {p : α → ι → Prop} (hic : #ι < c) :
    (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i := by
  simp only [Filter.Eventually, ofPred_forall]
  exact cardinal_iInter_mem hic
/-
**Filter.eventually_cardinal_ball** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：eventually_cardinal_ball {S : Set ι} (hS : #S < c) {p : α -> forall i in S
, Prop} : (forallᶠ x in l, forall i hi, p x i hi) ↔ forall i hi, forallᶠ x in l,
 p x i hi
参数：hS : #S < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.cardinal_bInter_mem`：cardinal_bInter_mem {S : Set ι} (hS : #S < c
) {s : forall i in S, Set α} : (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ forall i, fo
rall hi : i in S…
-/
theorem eventually_cardinal_ball {S : Set ι} (hS : #S < c)
    {p : α → ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i hi, p x i hi) ↔ ∀ i hi, ∀ᶠ x in l, p x i hi := by
  simp only [Filter.Eventually, ofPred_forall]
  exact cardinal_bInter_mem hS
/-
**Filter.EventuallyLE.cardinal_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventual
lyLE`。
形式化陈述：∀ {ι α : Type u} {c : Cardinal.{u}} {l : Filter α} [CardinalInterFilter l 
c] {s t : ι → Set α},   Cardinal.mk ι < c → (∀ (i : ι), s i ≤ᶠ[l] t i) → ⋃ i, s 
i ≤ᶠ[l] ⋃ i, t i
参数：∀ (i : ι), s i ≤ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_cardinal_forall`：eventually_cardinal_forall {p : α -> 
ι -> Prop} (hic : #ι < c) : (forallᶠ x in l, forall i, p x i) ↔ forall i, forall
ᶠ x in l, p x i
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem EventuallyLE.cardinal_iUnion {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i ≤ᶠ[l] t i) : ⋃ i, s i ≤ᶠ[l] ⋃ i, t i :=
  ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs => mem_iUnion.2 <|
    (mem_iUnion.1 hs).imp hst
/-
**Filter.EventuallyEq.cardinal_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventual
lyEq`。
形式化陈述：∀ {ι α : Type u} {c : Cardinal.{u}} {l : Filter α} [CardinalInterFilter l 
c] {s t : ι → Set α},   Cardinal.mk ι < c → (∀ (i : ι), s i =ᶠ[l] t i) → ⋃ i, s 
i =ᶠ[l] ⋃ i, t i
参数：∀ (i : ι), s i =ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyLE.cardinal_iUnion`：∀ {ι α : Type u} {c : Cardinal.{u}}
 {l : Filter α} [CardinalInterFilter l c] {s t : ι → Set α},   Cardinal.mk ι < c
 → (∀ (i : ι), s i ≤ᶠ[l] …
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem EventuallyEq.cardinal_iUnion {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i =ᶠ[l] t i) : ⋃ i, s i =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.cardinal_iUnion hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iUnion hic fun i => (h i).symm.le)
/-
**Filter.EventuallyLE.cardinal_bUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventual
lyLE`。
形式化陈述：∀ {ι α : Type u} {c : Cardinal.{u}} {l : Filter α} [CardinalInterFilter l 
c] {S : Set ι},   Cardinal.mk ↑S < c →     ∀ {s t : (i : ι) → i ∈ S → Set α},   
    (∀ (i : ι) (hi : i ∈ S), s i hi ≤ᶠ[l] t i hi) → ⋃ i, ⋃ (h : i ∈ S), s i h ≤ᶠ
[l] ⋃ i, ⋃ (h : i ∈ S), t i h
参数：i : ι；∀ (i : ι) (hi : i ∈ S), s i hi ≤ᶠ[l] t i hi；h : i ∈ S；h : i ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biUnion_eq_iUnion`：biUnion_eq_iUnion (s : Set α) (t : forall x in s,
 Set β) : ⋃ x in s, t x ‹_› = ⋃ x : s, t x x.2
· 使用定理 `Filter.EventuallyLE.cardinal_iUnion`：∀ {ι α : Type u} {c : Cardinal.{u}}
 {l : Filter α} [CardinalInterFilter l c] {s t : ι → Set α},   Cardinal.mk ι < c
 → (∀ (i : ι), s i ≤ᶠ[l] …
-/
theorem EventuallyLE.cardinal_bUnion {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› := by
  simp only [biUnion_eq_iUnion]
  exact EventuallyLE.cardinal_iUnion hS fun i => h i i.2
/-
**Filter.EventuallyEq.cardinal_bUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventual
lyEq`。
形式化陈述：∀ {ι α : Type u} {c : Cardinal.{u}} {l : Filter α} [CardinalInterFilter l 
c] {S : Set ι},   Cardinal.mk ↑S < c →     ∀ {s t : (i : ι) → i ∈ S → Set α},   
    (∀ (i : ι) (hi : i ∈ S), s i hi =ᶠ[l] t i hi) → ⋃ i, ⋃ (h : i ∈ S), s i h =ᶠ
[l] ⋃ i, ⋃ (h : i ∈ S), t i h
参数：i : ι；∀ (i : ι) (hi : i ∈ S), s i hi =ᶠ[l] t i hi；h : i ∈ S；h : i ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyLE.cardinal_bUnion`：∀ {ι α : Type u} {c : Cardinal.{u}}
 {l : Filter α} [CardinalInterFilter l c] {S : Set ι},   Cardinal.mk ↑S < c →   
  ∀ {s t : (i : ι) → i ∈ …
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem EventuallyEq.cardinal_bUnion {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bUnion hS fun i hi => (h i hi).symm.le)
/-
**Filter.EventuallyLE.cardinal_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventual
lyLE`。
形式化陈述：∀ {ι α : Type u} {c : Cardinal.{u}} {l : Filter α} [CardinalInterFilter l 
c] {s t : ι → Set α},   Cardinal.mk ι < c → (∀ (i : ι), s i ≤ᶠ[l] t i) → ⋂ i, s 
i ≤ᶠ[l] ⋂ i, t i
参数：∀ (i : ι), s i ≤ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_cardinal_forall`：eventually_cardinal_forall {p : α -> 
ι -> Prop} (hic : #ι < c) : (forallᶠ x in l, forall i, p x i) ↔ forall i, forall
ᶠ x in l, p x i
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem EventuallyLE.cardinal_iInter {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i ≤ᶠ[l] t i) : ⋂ i, s i ≤ᶠ[l] ⋂ i, t i :=
  ((eventually_cardinal_forall hic).2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)
/-
**Filter.EventuallyEq.cardinal_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventual
lyEq`。
形式化陈述：∀ {ι α : Type u} {c : Cardinal.{u}} {l : Filter α} [CardinalInterFilter l 
c] {s t : ι → Set α},   Cardinal.mk ι < c → (∀ (i : ι), s i =ᶠ[l] t i) → ⋂ i, s 
i =ᶠ[l] ⋂ i, t i
参数：∀ (i : ι), s i =ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyLE.cardinal_iInter`：∀ {ι α : Type u} {c : Cardinal.{u}}
 {l : Filter α} [CardinalInterFilter l c] {s t : ι → Set α},   Cardinal.mk ι < c
 → (∀ (i : ι), s i ≤ᶠ[l] …
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem EventuallyEq.cardinal_iInter {s t : ι → Set α} (hic : #ι < c)
    (h : ∀ i, s i =ᶠ[l] t i) : ⋂ i, s i =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.cardinal_iInter hic fun i => (h i).le).antisymm
    (EventuallyLE.cardinal_iInter hic fun i => (h i).symm.le)
/-
**Filter.EventuallyLE.cardinal_bInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventual
lyLE`。
形式化陈述：∀ {ι α : Type u} {c : Cardinal.{u}} {l : Filter α} [CardinalInterFilter l 
c] {S : Set ι},   Cardinal.mk ↑S < c →     ∀ {s t : (i : ι) → i ∈ S → Set α},   
    (∀ (i : ι) (hi : i ∈ S), s i hi ≤ᶠ[l] t i hi) → ⋂ i, ⋂ (h : i ∈ S), s i h ≤ᶠ
[l] ⋂ i, ⋂ (h : i ∈ S), t i h
参数：i : ι；∀ (i : ι) (hi : i ∈ S), s i hi ≤ᶠ[l] t i hi；h : i ∈ S；h : i ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `Filter.EventuallyLE.cardinal_iInter`：∀ {ι α : Type u} {c : Cardinal.{u}}
 {l : Filter α} [CardinalInterFilter l c] {s t : ι → Set α},   Cardinal.mk ι < c
 → (∀ (i : ι), s i ≤ᶠ[l] …
-/
theorem EventuallyLE.cardinal_bInter {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› := by
  simp only [biInter_eq_iInter]
  exact EventuallyLE.cardinal_iInter hS fun i => h i i.2
/-
**Filter.EventuallyEq.cardinal_bInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventual
lyEq`。
形式化陈述：∀ {ι α : Type u} {c : Cardinal.{u}} {l : Filter α} [CardinalInterFilter l 
c] {S : Set ι},   Cardinal.mk ↑S < c →     ∀ {s t : (i : ι) → i ∈ S → Set α},   
    (∀ (i : ι) (hi : i ∈ S), s i hi =ᶠ[l] t i hi) → ⋂ i, ⋂ (h : i ∈ S), s i h =ᶠ
[l] ⋂ i, ⋂ (h : i ∈ S), t i h
参数：i : ι；∀ (i : ι) (hi : i ∈ S), s i hi =ᶠ[l] t i hi；h : i ∈ S；h : i ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyLE.cardinal_bInter`：∀ {ι α : Type u} {c : Cardinal.{u}}
 {l : Filter α} [CardinalInterFilter l c] {S : Set ι},   Cardinal.mk ↑S < c →   
  ∀ {s t : (i : ι) → i ∈ …
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem EventuallyEq.cardinal_bInter {S : Set ι} (hS : #S < c)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.cardinal_bInter hS fun i hi => (h i hi).symm.le)

/-- Construct a filter with cardinal `c` intersection property. This constructor deduces
`Filter.univ_sets` and `Filter.inter_sets` from the cardinal `c` intersection property. -/
/-
**Filter.ofCardinalInter** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：ofCardinalInter (l : Set (Set α)) (hc : 2 < c) (hl : forall S : Set (Set α
), (#S < c) -> S subseteq l -> ⋂₀ S in l) (h_mono : forall s t, s in l -> s subs
eteq t -> t in l) : Filter α where sets
参数：l : Set (Set α)；hc : 2 < c；hl : forall S : Set (Set α), (#S < c) -> S subsete
q l -> ⋂₀ S in l；h_mono : forall s t, s in l -> s subseteq t -> t in l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a filter with cardinal `c` intersection property. This constructor ded
uces
`Filter.univ_sets` and `Filter.inter_sets` from the cardinal `c` intersection pr
operty.
-/
def ofCardinalInter (l : Set (Set α)) (hc : 2 < c)
    (hl : ∀ S : Set (Set α), (#S < c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets :=
    sInter_empty ▸ hl ∅ (mk_eq_zero (∅ : Set (Set α)) ▸ lt_trans zero_lt_two hc) (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸ by
    apply hl _ (?_) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
    have : #({s, t} : Set (Set α)) ≤ 2 := by
      calc
      _ ≤ #({t} : Set (Set α)) + 1 := Cardinal.mk_insert_le
      _ = 2 := by norm_num
    exact lt_of_le_of_lt this hc
/-
**Filter.cardinalInter_ofCardinalInter** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：cardinalInter_ofCardinalInter (l : Set (Set α)) (hc : 2 < c) (hl : forall 
S : Set (Set α), (#S < c) -> S subseteq l -> ⋂₀ S in l) (h_mono : forall s t, s 
in l -> s subseteq t -> t in l) : CardinalInterFilter (Filter.ofCardinalInter l 
hc hl h_mono) c
参数：l : Set (Set α)；hc : 2 < c；hl : forall S : Set (Set α), (#S < c) -> S subsete
q l -> ⋂₀ S in l；h_mono : forall s t, s in l -> s subseteq t -> t in l。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
instance cardinalInter_ofCardinalInter (l : Set (Set α)) (hc : 2 < c)
    (hl : ∀ S : Set (Set α), (#S < c) → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CardinalInterFilter (Filter.ofCardinalInter l hc hl h_mono) c :=
  ⟨hl⟩

@[simp]
/-
**Filter.mem_ofCardinalInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_ofCardinalInter {l : Set (Set α)} (hc : 2 < c) (hl : forall S : Set (S
et α), (#S < c) -> S subseteq l -> ⋂₀ S in l) (h_mono : forall s t, s in l -> s 
subseteq t -> t in l) {s : Set α} : s in Filter.ofCardinalInter l hc hl h_mono ↔
 s in l
参数：Set α；hc : 2 < c；hl : forall S : Set (Set α), (#S < c) -> S subseteq l -> ⋂₀ 
S in l；h_mono : forall s t, s in l -> s subseteq t -> t in l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ofCardinalInter {l : Set (Set α)} (hc : 2 < c)
    (hl : ∀ S : Set (Set α), (#S < c) → S ⊆ l → ⋂₀ S ∈ l) (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l)
    {s : Set α} : s ∈ Filter.ofCardinalInter l hc hl h_mono ↔ s ∈ l :=
  Iff.rfl

/-- Construct a filter with cardinal `c` intersection property.
Similarly to `Filter.comk`, a set belongs to this filter if its complement satisfies the property.
Similarly to `Filter.ofCardinalInter`,
this constructor deduces some properties from the cardinal `c` intersection property
which becomes the cardinal `c` union property because we take complements of all sets. -/
/-
**Filter.ofCardinalUnion** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：ofCardinalUnion (l : Set (Set α)) (hc : 2 < c) (hUnion : forall S : Set (S
et α), (#S < c) -> (forall s in S, s in l) -> ⋃₀ S in l) (hmono : forall t in l,
 forall s subseteq t, s in l) : Filter α
参数：l : Set (Set α)；hc : 2 < c；hUnion : forall S : Set (Set α), (#S < c) -> (fora
ll s in S, s in l) -> ⋃₀ S in l；hmono : forall t in l, forall s subseteq t, s in
 l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a filter with cardinal `c` intersection property.
Similarly to `Filter.comk`, a set belongs to this filter if its complement satis
fies the property.
Similarly to `Filter.ofCardinalInter`,
this constructor deduces some properties from the cardinal `c` intersection prop
erty
which becomes the cardinal `c` union property because we take complements of all
 sets.
-/
def ofCardinalUnion (l : Set (Set α)) (hc : 2 < c)
    (hUnion : ∀ S : Set (Set α), (#S < c) → (∀ s ∈ S, s ∈ l) → ⋃₀ S ∈ l)
    (hmono : ∀ t ∈ l, ∀ s ⊆ t, s ∈ l) : Filter α := by
  refine .ofCardinalInter {s | sᶜ ∈ l} hc (fun S hSc hSp ↦ ?_) fun s t ht hsub ↦ ?_
  · rw [mem_ofPred_eq, compl_sInter]
    apply hUnion (compl '' S) (lt_of_le_of_lt mk_image_le hSc)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_ofPred_eq]
    rw [← compl_subset_compl] at hsub
    exact hmono sᶜ ht tᶜ hsub
/-
**Filter.cardinalInter_ofCardinalUnion** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：cardinalInter_ofCardinalUnion (l : Set (Set α)) (hc : 2 < c) (h₁ h₂) : Car
dinalInterFilter (Filter.ofCardinalUnion l hc h₁ h₂) c
参数：l : Set (Set α)；hc : 2 < c；h₁ h₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
instance cardinalInter_ofCardinalUnion (l : Set (Set α)) (hc : 2 < c) (h₁ h₂) :
    CardinalInterFilter (Filter.ofCardinalUnion l hc h₁ h₂) c :=
  cardinalInter_ofCardinalInter ..

@[simp]
/-
**Filter.mem_ofCardinalUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_ofCardinalUnion {l : Set (Set α)} (hc : 2 < c) {hunion hmono s} : s in
 ofCardinalUnion l hc hunion hmono ↔ l sᶜ
参数：Set α；hc : 2 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ofCardinalUnion {l : Set (Set α)} (hc : 2 < c) {hunion hmono s} :
    s ∈ ofCardinalUnion l hc hunion hmono ↔ l sᶜ :=
  Iff.rfl
/-
**Filter.cardinalInterFilter_principal** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：cardinalInterFilter_principal (s : Set α) : CardinalInterFilter (𝓟 s) c
参数：s : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_sInter`：subset_sInter {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t subseteq t') : t subseteq ⋂₀ S
-/
instance cardinalInterFilter_principal (s : Set α) : CardinalInterFilter (𝓟 s) c :=
  ⟨fun _ _ hS => subset_sInter hS⟩
/-
**Filter.cardinalInterFilter_bot** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：cardinalInterFilter_bot : CardinalInterFilter (⊥ : Filter α) c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
-/
instance cardinalInterFilter_bot : CardinalInterFilter (⊥ : Filter α) c := by
  rw [← principal_empty]
  apply cardinalInterFilter_principal
/-
**Filter.cardinalInterFilter_top** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：cardinalInterFilter_top : CardinalInterFilter (⊤ : Filter α) c
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
-/
instance cardinalInterFilter_top : CardinalInterFilter (⊤ : Filter α) c := by
  rw [← principal_univ]
  apply cardinalInterFilter_principal
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (l : Filter β) [CardinalInterFilter l c] (f : α → β) :
    CardinalInterFilter (comap f l) c := by
  refine ⟨fun S hSc hS => ?_⟩
  choose! t htl ht using hS
  refine ⟨_, (cardinal_bInter_mem hSc).2 htl, ?_⟩
  simpa [preimage_iInter] using iInter₂_mono ht
/-
**Filter.** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (l : Filter α) [CardinalInterFilter l c] (f : α → β) :
    CardinalInterFilter (map f l) c := by
  refine ⟨fun S hSc hS => ?_⟩
  simp only [mem_map, sInter_eq_biInter, preimage_iInter₂] at hS ⊢
  exact (cardinal_bInter_mem hSc).2 hS

/-- Infimum of two `CardinalInterFilter`s is a `CardinalInterFilter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
/-
**Filter.cardinalInterFilter_inf_eq** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：cardinalInterFilter_inf_eq (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c] [
CardinalInterFilter l₂ c] : CardinalInterFilter (l₁ ⊓ l₂) c
参数：l₁ l₂ : Filter α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.cardinal_bInter_mem`：cardinal_bInter_mem {S : Set ι} (hS : #S < c
) {s : forall i in S, Set α} : (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ forall i, fo
rall hi : i in S…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.inter_mem_inf`：inter_mem_inf {α : Type u} {f g : Filter α} {s t :
 Set α} (hs : s in f) (ht : t in g) : s inter t in f ⊓ g
· 使用定理 `Set.subset_sInter`：subset_sInter {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t subseteq t') : t subseteq ⋂₀ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `Set.iInter_subset_of_subset`：iInter_subset_of_subset {s : ι -> Set α} {t
 : Set α} (i : ι) (h : s i subseteq t) : ⋂ i, s i subseteq t
· 使用定理 `Set.iInter_subset`：iInter_subset : forall (s : ι -> Set β) (i : ι), ⋂ i,
 s i subseteq s i
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Infimum of two `CardinalInterFilter`s is a `CardinalInterFilter`. This is useful
, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`.
-/
instance cardinalInterFilter_inf_eq (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c]
    [CardinalInterFilter l₂ c] : CardinalInterFilter (l₁ ⊓ l₂) c := by
  refine ⟨fun S hSc hS => ?_⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i ∈ S, s i ‹_›) ∈ l₁ := (cardinal_bInter_mem hSc).2 hs
  replace ht : (⋂ i ∈ S, t i ‹_›) ∈ l₂ := (cardinal_bInter_mem hSc).2 ht
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => ?_)
  rw [hst i hi]
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)
/-
**Filter.cardinalInterFilter_inf** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：cardinalInterFilter_inf (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}} [Cardina
lInterFilter l₁ c₁] [CardinalInterFilter l₂ c₂] : CardinalInterFilter (l₁ ⊓ l₂) 
(c₁ ⊓ c₂)
参数：l₁ l₂ : Filter α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CardinalInterFilter.of_cardinalInterFilter_of_le`：CardinalInterFilter.of
_cardinalInterFilter_of_le (l : Filter α) [CardinalInterFilter l c] {a : Cardina
l.{u}} (hac : a <= c) : CardinalInterF…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
instance cardinalInterFilter_inf (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}}
    [CardinalInterFilter l₁ c₁] [CardinalInterFilter l₂ c₂] : CardinalInterFilter (l₁ ⊓ l₂)
    (c₁ ⊓ c₂) := by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_inf_eq _ _

/-- Supremum of two `CardinalInterFilter`s is a `CardinalInterFilter`. -/
/-
**Filter.cardinalInterFilter_sup_eq** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：cardinalInterFilter_sup_eq (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c] [
CardinalInterFilter l₂ c] : CardinalInterFilter (l₁ ⊔ l₂) c
参数：l₁ l₂ : Filter α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `cardinal_sInter_mem`：cardinal_sInter_mem {S : Set (Set α)} [CardinalInte
rFilter l c] (hSc : #S < c) : ⋂₀ S in l ↔ forall s in S, s in l
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Supremum of two `CardinalInterFilter`s is a `CardinalInterFilter`.
-/
instance cardinalInterFilter_sup_eq (l₁ l₂ : Filter α) [CardinalInterFilter l₁ c]
    [CardinalInterFilter l₂ c] : CardinalInterFilter (l₁ ⊔ l₂) c := by
  refine ⟨fun S hSc hS => ⟨?_, ?_⟩⟩ <;> refine (cardinal_sInter_mem hSc).2 fun s hs => ?_
  exacts [(hS s hs).1, (hS s hs).2]
/-
**Filter.cardinalInterFilter_sup** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：cardinalInterFilter_sup (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}} [Cardina
lInterFilter l₁ c₁] [CardinalInterFilter l₂ c₂] : CardinalInterFilter (l₁ ⊔ l₂) 
(c₁ ⊓ c₂)
参数：l₁ l₂ : Filter α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CardinalInterFilter.of_cardinalInterFilter_of_le`：CardinalInterFilter.of
_cardinalInterFilter_of_le (l : Filter α) [CardinalInterFilter l c] {a : Cardina
l.{u}} (hac : a <= c) : CardinalInterF…
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
instance cardinalInterFilter_sup (l₁ l₂ : Filter α) {c₁ c₂ : Cardinal.{u}}
    [CardinalInterFilter l₁ c₁] [CardinalInterFilter l₂ c₂] :
    CardinalInterFilter (l₁ ⊔ l₂) (c₁ ⊓ c₂) := by
  have : CardinalInterFilter l₁ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₁ inf_le_left
  have : CardinalInterFilter l₂ (c₁ ⊓ c₂) :=
    CardinalInterFilter.of_cardinalInterFilter_of_le l₂ inf_le_right
  exact cardinalInterFilter_sup_eq _ _

variable (g : Set (Set α))

/-- `Filter.CardinalGenerateSets c g` is the (sets of the)
greatest `cardinalInterFilter c` containing `g`. -/
/-
**Filter.CardinalGenerateSets** 是 Mathlib 中的一个归纳类型，位于命名空间 `Filter`。
形式化陈述：{α : Type u} → {c : Cardinal.{u}} → Set (Set α) → Set α → Prop
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Filter.CardinalGenerateSets c g` is the (sets of the)
greatest `cardinalInterFilter c` containing `g`.
-/
inductive CardinalGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → CardinalGenerateSets s
  | univ : CardinalGenerateSets univ
  | superset {s t : Set α} : CardinalGenerateSets s → s ⊆ t → CardinalGenerateSets t
  | sInter {S : Set (Set α)} :
    (#S < c) → (∀ s ∈ S, CardinalGenerateSets s) → CardinalGenerateSets (⋂₀ S)

/-- Assuming `2 < c`, `Filter.cardinalGenerate c g` is the greatest `CardinalInterFilter c`
containing `g`. -/
/-
**Filter.cardinalGenerate** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：cardinalGenerate (hc : 2 < c) : Filter α
参数：hc : 2 < c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assuming `2 < c`, `Filter.cardinalGenerate c g` is the greatest `CardinalInterFi
lter c`
containing `g`.
-/
def cardinalGenerate (hc : 2 < c) : Filter α :=
  ofCardinalInter {s | CardinalGenerateSets g s} hc (fun _ => .sInter) fun _ _ => .superset
/-
**Filter.cardinalInter_ofCardinalGenerate** 是 Mathlib 中的一个引理，位于命名空间 `Filter`。
形式化陈述：cardinalInter_ofCardinalGenerate (hc : 2 < c) : CardinalInterFilter (cardi
nalGenerate g hc) c
参数：hc : 2 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma cardinalInter_ofCardinalGenerate (hc : 2 < c) :
    CardinalInterFilter (cardinalGenerate g hc) c := by
  delta cardinalGenerate
  apply cardinalInter_ofCardinalInter _ _ _

variable {g}

/-- A set is in the `cardinalInterFilter` generated by `g` if and only if
it contains an intersection of `c` elements of `g`. -/
/-
**Filter.mem_cardinalGenerate_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_cardinalGenerate_iff {s : Set α} {hreg : c.IsRegular} : s in cardinalG
enerate g (IsRegular.nat_lt hreg 2) ↔ exists S : Set (Set α), S subseteq g ∧ (#S
 < c) ∧ ⋂₀ S subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.IsRegular.nat_lt`：∀ {c : Cardinal.{u_1}}, c.IsRegular → ∀ (n : 
ℕ), ↑n < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Set.sInter_singleton`：sInter_singleton (s : Set α) : ⋂₀ {s} = s
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Cardinal.card_biUnion_lt_iff_forall_of_isRegular`：card_biUnion_lt_iff_fo
rall_of_isRegular {α β : Type u} {s : Set α} {t : forall a in s, Set β} (hc : c.
IsRegular) (hs : #s < c) : #(⋃ a in s,…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.subset_sInter`：subset_sInter {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t subseteq t') : t subseteq ⋂₀ S
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.sInter_subset_sInter`：sInter_subset_sInter {S T : Set (Set α)} (h : 
S subseteq T) : ⋂₀ T subseteq ⋂₀ S
· 使用定理 `Set.subset_iUnion₂`：subset_iUnion₂ {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : s i j subseteq ⋃ (i') (j'), s i' j'
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `Filter.cardinalInter_ofCardinalGenerate`：cardinalInter_ofCardinalGenerat
e (hc : 2 < c) : CardinalInterFilter (cardinalGenerate g hc) c
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
A set is in the `cardinalInterFilter` generated by `g` if and only if
it contains an intersection of `c` elements of `g`.
-/
theorem mem_cardinalGenerate_iff {s : Set α} {hreg : c.IsRegular} :
    s ∈ cardinalGenerate g (IsRegular.nat_lt hreg 2) ↔
    ∃ S : Set (Set α), S ⊆ g ∧ (#S < c) ∧ ⋂₀ S ⊆ s := by
  constructor <;> intro h
  · induction h with
    | @basic s hs =>
      refine ⟨{s}, singleton_subset_iff.mpr hs, ?_⟩
      simpa [subset_refl] using IsRegular.nat_lt hreg 1
    | univ =>
      exact ⟨∅, ⟨empty_subset g, mk_eq_zero (∅ : Set <| Set α) ▸ IsRegular.nat_lt hreg 0, by simp⟩⟩
    | superset _ _ ih => exact Exists.imp (by tauto) ih
    | @sInter S Sct _ ih =>
      choose T Tg Tct hT using ih
      refine ⟨⋃ (s) (H : s ∈ S), T s H, by simpa,
        (Cardinal.card_biUnion_lt_iff_forall_of_isRegular hreg Sct).2 Tct, ?_⟩
      apply subset_sInter
      apply fun s H => subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  have : CardinalInterFilter (cardinalGenerate g (IsRegular.nat_lt hreg 2)) c :=
    cardinalInter_ofCardinalGenerate _ _
  exact mem_of_superset ((cardinal_sInter_mem Sct).mpr
    (fun s H => CardinalGenerateSets.basic (Sg H))) hS
/-
**Filter.le_cardinalGenerate_iff_of_cardinalInterFilter** 是 Mathlib 中的一个定理，位于命名空
间 `Filter`。
形式化陈述：le_cardinalGenerate_iff_of_cardinalInterFilter {f : Filter α} [CardinalInt
erFilter f c] (hc : 2 < c) : f <= cardinalGenerate g hc ↔ g subseteq f.sets
参数：hc : 2 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `cardinal_sInter_mem`：cardinal_sInter_mem {S : Set (Set α)} [CardinalInte
rFilter l c] (hSc : #S < c) : ⋂₀ S in l ↔ forall s in S, s in l
-/
theorem le_cardinalGenerate_iff_of_cardinalInterFilter {f : Filter α} [CardinalInterFilter f c]
    (hc : 2 < c) : f ≤ cardinalGenerate g hc ↔ g ⊆ f.sets := by
  constructor <;> intro h
  · exact subset_trans (fun s => CardinalGenerateSets.basic) h
  intro s hs
  induction hs with
  | basic hs => exact h hs
  | univ => exact univ_mem
  | superset _ st ih => exact mem_of_superset ih st
  | sInter Sct _ ih => exact (cardinal_sInter_mem Sct).mpr ih

/-- `cardinalGenerate g hc` is the greatest `CardinalInterFilter c` containing `g`. -/
/-
**Filter.cardinalGenerate_isGreatest** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：cardinalGenerate_isGreatest (hc : 2 < c) : IsGreatest { f : Filter α | Car
dinalInterFilter f c ∧ g subseteq f.sets } (cardinalGenerate g hc)
参数：hc : 2 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Filter.cardinalInter_ofCardinalGenerate`：cardinalInter_ofCardinalGenerat
e (hc : 2 < c) : CardinalInterFilter (cardinalGenerate g hc) c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_cardinalGenerate_iff_of_cardinalInterFilter`：le_cardinalGenera
te_iff_of_cardinalInterFilter {f : Filter α} [CardinalInterFilter f c] (hc : 2 <
 c) : f <= cardinalGenerate g hc ↔ g subset…

--- 原说明 ---
`cardinalGenerate g hc` is the greatest `CardinalInterFilter c` containing `g`.
-/
theorem cardinalGenerate_isGreatest (hc : 2 < c) :
    IsGreatest { f : Filter α | CardinalInterFilter f c ∧ g ⊆ f.sets } (cardinalGenerate g hc) := by
  refine ⟨⟨cardinalInter_ofCardinalGenerate _ _, fun s => CardinalGenerateSets.basic⟩, ?_⟩
  rintro f ⟨fct, hf⟩
  rwa [le_cardinalGenerate_iff_of_cardinalInterFilter]

end Filter

