/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Filter.Curry
public import Mathlib.Data.Set.Countable

/-!
# Filters with countable intersection property

In this file we define `CountableInterFilter` to be the class of filters with the following
property: for any countable collection of sets `s ∈ l` their intersection belongs to `l` as well.

Two main examples are the `residual` filter defined in `Mathlib/Topology/GDelta/Basic.lean` and
the `MeasureTheory.ae` filter defined in `Mathlib/MeasureTheory/OuterMeasure/AE.lean`.

We reformulate the definition in terms of indexed intersection and in terms of `Filter.Eventually`
and provide instances for some basic constructions (`⊥`, `⊤`, `Filter.principal`, `Filter.map`,
`Filter.comap`, `Inf.inf`). We also provide a custom constructor `Filter.ofCountableInter`
that deduces two axioms of a `Filter` from the countable intersection property.

Note that there also exists a typeclass `CardinalInterFilter`, and thus an alternative spelling of
`CountableInterFilter` as `CardinalInterFilter l ℵ₁`. The former (defined here) is the
preferred spelling; it has the advantage of not requiring the user to import the theory of ordinals.

## Tags
filter, countable
-/

@[expose] public section


open Set Filter

variable {ι : Sort*} {α β : Type*}

/-- A filter `l` has the countable intersection property if for any countable collection
of sets `s ∈ l` their intersection belongs to `l` as well. -/
/-
**CountableInterFilter** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_2} → Filter α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A filter `l` has the countable intersection property if for any countable collec
tion
of sets `s ∈ l` their intersection belongs to `l` as well.
-/
class CountableInterFilter (l : Filter α) : Prop where
  /-- For a countable collection of sets `s ∈ l`, their intersection belongs to `l` as well. -/
  countable_sInter_mem : ∀ S : Set (Set α), S.Countable → (∀ s ∈ S, s ∈ l) → ⋂₀ S ∈ l

variable {l : Filter α} [CountableInterFilter l]
/-
**countable_sInter_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_sInter_mem {S : Set (Set α)} (hSc : S.Countable) : ⋂₀ S in l ↔ f
orall s in S, s in l
参数：Set α；hSc : S.Countable。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
· 使用定理 `CountableInterFilter.countable_sInter_mem`：∀ {α : Type u_2} {l : Filter 
α} [self : CountableInterFilter l] (S : Set (Set α)),   S.Countable → (∀ s ∈ S, 
s ∈ l) → ⋂₀ S ∈ l
-/
theorem countable_sInter_mem {S : Set (Set α)} (hSc : S.Countable) : ⋂₀ S ∈ l ↔ ∀ s ∈ S, s ∈ l :=
  ⟨fun hS _s hs => mem_of_superset hS (sInter_subset_of_mem hs),
    CountableInterFilter.countable_sInter_mem _ hSc⟩
/-
**countable_iInter_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_iInter_mem [Countable ι] {s : ι -> Set α} : (⋂ i, s i) in l ↔ fo
rall i, s i in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `countable_sInter_mem`：countable_sInter_mem {S : Set (Set α)} (hSc : S.Co
untable) : ⋂₀ S in l ↔ forall s in S, s in l
· 使用定理 `Set.countable_range`：countable_range [Countable ι] (f : ι -> β) : (range
 f).Countable
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `Set.sInter_range`：sInter_range (f : ι -> Set β) : ⋂₀ range f = ⋂ x, f x
-/
theorem countable_iInter_mem [Countable ι] {s : ι → Set α} : (⋂ i, s i) ∈ l ↔ ∀ i, s i ∈ l :=
  sInter_range s ▸ (countable_sInter_mem (countable_range _)).trans forall_mem_range
/-
**countable_bInter_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：countable_bInter_mem {ι : Type*} {S : Set ι} (hS : S.Countable) {s : foral
l i in S, Set α} : (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ forall i, forall hi : i 
in S, s i ‹_› in l
参数：hS : S.Countable。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.biInter_eq_iInter`：biInter_eq_iInter (s : Set α) (t : forall x in s,
 Set β) : ⋂ x in s, t x ‹_› = ⋂ x : s, t x x.2
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `countable_iInter_mem`：countable_iInter_mem [Countable ι] {s : ι -> Set α
} : (⋂ i, s i) in l ↔ forall i, s i in l
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
theorem countable_bInter_mem {ι : Type*} {S : Set ι} (hS : S.Countable) {s : ∀ i ∈ S, Set α} :
    (⋂ i, ⋂ hi : i ∈ S, s i ‹_›) ∈ l ↔ ∀ i, ∀ hi : i ∈ S, s i ‹_› ∈ l := by
  rw [biInter_eq_iInter]
  have := hS.toEncodable
  exact countable_iInter_mem.trans Subtype.forall
/-
**eventually_countable_forall** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_countable_forall [Countable ι] {p : α -> ι -> Prop} : (forallᶠ 
x in l, forall i, p x i) ↔ forall i, forallᶠ x in l, p x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `countable_iInter_mem`：countable_iInter_mem [Countable ι] {s : ι -> Set α
} : (⋂ i, s i) in l ↔ forall i, s i in l
-/
theorem eventually_countable_forall [Countable ι] {p : α → ι → Prop} :
    (∀ᶠ x in l, ∀ i, p x i) ↔ ∀ i, ∀ᶠ x in l, p x i := by
  simpa only [Filter.Eventually, ofPred_forall] using
    @countable_iInter_mem _ _ l _ _ fun i => { x | p x i }
/-
**eventually_countable_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_countable_ball {ι : Type*} {S : Set ι} (hS : S.Countable) {p : 
α -> forall i in S, Prop} : (forallᶠ x in l, forall i hi, p x i hi) ↔ forall i h
i, forallᶠ x in l, p x i hi
参数：hS : S.Countable。
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
· 使用定理 `countable_bInter_mem`：countable_bInter_mem {ι : Type*} {S : Set ι} (hS :
 S.Countable) {s : forall i in S, Set α} : (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ 
forall i, …
-/
theorem eventually_countable_ball {ι : Type*} {S : Set ι} (hS : S.Countable)
    {p : α → ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i hi, p x i hi) ↔ ∀ i hi, ∀ᶠ x in l, p x i hi := by
  simpa only [Filter.Eventually, ofPred_forall] using
    @countable_bInter_mem _ l _ _ _ hS fun i hi => { x | p x i hi }
/-
**eventually_finset_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eventually_finset_ball {ι : Type*} {S : Finset ι} {p : α -> forall i in S,
 Prop} : (forallᶠ x in l, forall i hi, p x i hi) ↔ forall i hi, forallᶠ x in l, 
p x i hi
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eventually_countable_ball`：eventually_countable_ball {ι : Type*} {S : Se
t ι} (hS : S.Countable) {p : α -> forall i in S, Prop} : (forallᶠ x in l, forall
 i hi, p x i hi…
· 使用定理 `Finset.countable_toSet`：Finset.countable_toSet (s : Finset α) : Set.Coun
table (↑s : Set α)
-/
theorem eventually_finset_ball {ι : Type*} {S : Finset ι} {p : α → ∀ i ∈ S, Prop} :
    (∀ᶠ x in l, ∀ i hi, p x i hi) ↔ ∀ i hi, ∀ᶠ x in l, p x i hi :=
  eventually_countable_ball S.countable_toSet

namespace Filter

/-
**Filter.EventuallyLE.countable_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventua
llyLE`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} {l : Filter α} [CountableInterFilter l] [C
ountable ι] {s t : ι → Set α},   (∀ (i : ι), s i ≤ᶠ[l] t i) → ⋃ i, s i ≤ᶠ[l] ⋃ i
, t i
参数：∀ (i : ι), s i ≤ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_countable_forall`：eventually_countable_forall [Countable ι] {
p : α -> ι -> Prop} : (forallᶠ x in l, forall i, p x i) ↔ forall i, forallᶠ x in
 l, p x i
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem EventuallyLE.countable_iUnion [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    ⋃ i, s i ≤ᶠ[l] ⋃ i, t i :=
  (eventually_countable_forall.2 h).mono fun _ hst hs => mem_iUnion.2 <| (mem_iUnion.1 hs).imp hst

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_iUnion :=
  EventuallyLE.countable_iUnion
/-
**Filter.EventuallyEq.countable_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventua
llyEq`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} {l : Filter α} [CountableInterFilter l] [C
ountable ι] {s t : ι → Set α},   (∀ (i : ι), s i =ᶠ[l] t i) → ⋃ i, s i =ᶠ[l] ⋃ i
, t i
参数：∀ (i : ι), s i =ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyLE.countable_iUnion`：∀ {ι : Sort u_1} {α : Type u_2} {l
 : Filter α} [CountableInterFilter l] [Countable ι] {s t : ι → Set α},   (∀ (i :
 ι), s i ≤ᶠ[l] t i) → ⋃ i,…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem EventuallyEq.countable_iUnion [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    ⋃ i, s i =ᶠ[l] ⋃ i, t i :=
  (EventuallyLE.countable_iUnion fun i => (h i).le).antisymm
    (EventuallyLE.countable_iUnion fun i => (h i).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_iUnion :=
  EventuallyEq.countable_iUnion
/-
**Filter.EventuallyLE.countable_bUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventua
llyLE`。
形式化陈述：∀ {α : Type u_2} {l : Filter α} [CountableInterFilter l] {ι : Type u_4} {S
 : Set ι},   S.Countable →     ∀ {s t : (i : ι) → i ∈ S → Set α},       (∀ (i : 
ι) (hi : i ∈ S), s i hi ≤ᶠ[l] t i hi) → ⋃ i, ⋃ (h : i ∈ S), s i h ≤ᶠ[l] ⋃ i, ⋃ (
h : i ∈ S), t i h
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
· 使用定理 `Filter.EventuallyLE.countable_iUnion`：∀ {ι : Sort u_1} {α : Type u_2} {l
 : Filter α} [CountableInterFilter l] [Countable ι] {s t : ι → Set α},   (∀ (i :
 ι), s i ≤ᶠ[l] t i) → ⋃ i,…
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
-/
theorem EventuallyLE.countable_bUnion {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› ≤ᶠ[l] ⋃ i ∈ S, t i ‹_› := by
  simp only [biUnion_eq_iUnion]
  have := hS.toEncodable
  exact EventuallyLE.countable_iUnion fun i => h i i.2

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_bUnion :=
  EventuallyLE.countable_bUnion
/-
**Filter.EventuallyEq.countable_bUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventua
llyEq`。
形式化陈述：∀ {α : Type u_2} {l : Filter α} [CountableInterFilter l] {ι : Type u_4} {S
 : Set ι},   S.Countable →     ∀ {s t : (i : ι) → i ∈ S → Set α},       (∀ (i : 
ι) (hi : i ∈ S), s i hi =ᶠ[l] t i hi) → ⋃ i, ⋃ (h : i ∈ S), s i h =ᶠ[l] ⋃ i, ⋃ (
h : i ∈ S), t i h
参数：i : ι；∀ (i : ι) (hi : i ∈ S), s i hi =ᶠ[l] t i hi；h : i ∈ S；h : i ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyLE.countable_bUnion`：∀ {α : Type u_2} {l : Filter α} [C
ountableInterFilter l] {ι : Type u_4} {S : Set ι},   S.Countable →     ∀ {s t : 
(i : ι) → i ∈ S → Set α}, …
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem EventuallyEq.countable_bUnion {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋃ i ∈ S, s i ‹_› =ᶠ[l] ⋃ i ∈ S, t i ‹_› :=
  (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bUnion hS fun i hi => (h i hi).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_bUnion :=
  EventuallyEq.countable_bUnion
/-
**Filter.EventuallyLE.countable_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventua
llyLE`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} {l : Filter α} [CountableInterFilter l] [C
ountable ι] {s t : ι → Set α},   (∀ (i : ι), s i ≤ᶠ[l] t i) → ⋂ i, s i ≤ᶠ[l] ⋂ i
, t i
参数：∀ (i : ι), s i ≤ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_countable_forall`：eventually_countable_forall [Countable ι] {
p : α -> ι -> Prop} : (forallᶠ x in l, forall i, p x i) ↔ forall i, forallᶠ x in
 l, p x i
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem EventuallyLE.countable_iInter [Countable ι] {s t : ι → Set α} (h : ∀ i, s i ≤ᶠ[l] t i) :
    ⋂ i, s i ≤ᶠ[l] ⋂ i, t i :=
  (eventually_countable_forall.2 h).mono fun _ hst hs =>
    mem_iInter.2 fun i => hst _ (mem_iInter.1 hs i)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_iInter :=
  EventuallyLE.countable_iInter
/-
**Filter.EventuallyEq.countable_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventua
llyEq`。
形式化陈述：∀ {ι : Sort u_1} {α : Type u_2} {l : Filter α} [CountableInterFilter l] [C
ountable ι] {s t : ι → Set α},   (∀ (i : ι), s i =ᶠ[l] t i) → ⋂ i, s i =ᶠ[l] ⋂ i
, t i
参数：∀ (i : ι), s i =ᶠ[l] t i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyLE.countable_iInter`：∀ {ι : Sort u_1} {α : Type u_2} {l
 : Filter α} [CountableInterFilter l] [Countable ι] {s t : ι → Set α},   (∀ (i :
 ι), s i ≤ᶠ[l] t i) → ⋂ i,…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem EventuallyEq.countable_iInter [Countable ι] {s t : ι → Set α} (h : ∀ i, s i =ᶠ[l] t i) :
    ⋂ i, s i =ᶠ[l] ⋂ i, t i :=
  (EventuallyLE.countable_iInter fun i => (h i).le).antisymm
    (EventuallyLE.countable_iInter fun i => (h i).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_iInter :=
  EventuallyEq.countable_iInter
/-
**Filter.EventuallyLE.countable_bInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventua
llyLE`。
形式化陈述：∀ {α : Type u_2} {l : Filter α} [CountableInterFilter l] {ι : Type u_4} {S
 : Set ι},   S.Countable →     ∀ {s t : (i : ι) → i ∈ S → Set α},       (∀ (i : 
ι) (hi : i ∈ S), s i hi ≤ᶠ[l] t i hi) → ⋂ i, ⋂ (h : i ∈ S), s i h ≤ᶠ[l] ⋂ i, ⋂ (
h : i ∈ S), t i h
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
· 使用定理 `Filter.EventuallyLE.countable_iInter`：∀ {ι : Sort u_1} {α : Type u_2} {l
 : Filter α} [CountableInterFilter l] [Countable ι] {s t : ι → Set α},   (∀ (i :
 ι), s i ≤ᶠ[l] t i) → ⋂ i,…
· 使用定理 `Encodable.countable`：∀ {α : Type u_1} [Encodable α], Countable α
-/
theorem EventuallyLE.countable_bInter {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi ≤ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› ≤ᶠ[l] ⋂ i ∈ S, t i ‹_› := by
  simp only [biInter_eq_iInter]
  have := hS.toEncodable
  exact EventuallyLE.countable_iInter fun i => h i i.2

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyLE.countable_bInter :=
  EventuallyLE.countable_bInter
/-
**Filter.EventuallyEq.countable_bInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Eventua
llyEq`。
形式化陈述：∀ {α : Type u_2} {l : Filter α} [CountableInterFilter l] {ι : Type u_4} {S
 : Set ι},   S.Countable →     ∀ {s t : (i : ι) → i ∈ S → Set α},       (∀ (i : 
ι) (hi : i ∈ S), s i hi =ᶠ[l] t i hi) → ⋂ i, ⋂ (h : i ∈ S), s i h =ᶠ[l] ⋂ i, ⋂ (
h : i ∈ S), t i h
参数：i : ι；∀ (i : ι) (hi : i ∈ S), s i hi =ᶠ[l] t i hi；h : i ∈ S；h : i ∈ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyLE.antisymm`：∀ {α : Type u} {β : Type v} [inst : Partia
lOrder β] {l : Filter α} {f g : α → β}, f ≤ᶠ[l] g → g ≤ᶠ[l] f → f =ᶠ[l] g
· 使用定理 `Filter.EventuallyLE.countable_bInter`：∀ {α : Type u_2} {l : Filter α} [C
ountableInterFilter l] {ι : Type u_4} {S : Set ι},   S.Countable →     ∀ {s t : 
(i : ι) → i ∈ S → Set α}, …
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
-/
theorem EventuallyEq.countable_bInter {ι : Type*} {S : Set ι} (hS : S.Countable)
    {s t : ∀ i ∈ S, Set α} (h : ∀ i hi, s i hi =ᶠ[l] t i hi) :
    ⋂ i ∈ S, s i ‹_› =ᶠ[l] ⋂ i ∈ S, t i ‹_› :=
  (EventuallyLE.countable_bInter hS fun i hi => (h i hi).le).antisymm
    (EventuallyLE.countable_bInter hS fun i hi => (h i hi).symm.le)

@[deprecated (since := "2026-03-03")] alias _root_.EventuallyEq.countable_bInter :=
  EventuallyEq.countable_bInter

/-- Construct a filter with countable intersection property. This constructor deduces
`Filter.univ_sets` and `Filter.inter_sets` from the countable intersection property. -/
/-
**Filter.ofCountableInter** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：ofCountableInter (l : Set (Set α)) (hl : forall S : Set (Set α), S.Countab
le -> S subseteq l -> ⋂₀ S in l) (h_mono : forall s t, s in l -> s subseteq t ->
 t in l) : Filter α where sets
参数：l : Set (Set α)；hl : forall S : Set (Set α), S.Countable -> S subseteq l -> ⋂
₀ S in l；h_mono : forall s t, s in l -> s subseteq t -> t in l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a filter with countable intersection property. This constructor deduce
s
`Filter.univ_sets` and `Filter.inter_sets` from the countable intersection prope
rty.
-/
def ofCountableInter (l : Set (Set α))
    (hl : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) : Filter α where
  sets := l
  univ_sets := @sInter_empty α ▸ hl _ countable_empty (empty_subset _)
  sets_of_superset := h_mono _ _
  inter_sets {s t} hs ht := sInter_pair s t ▸
    hl _ ((countable_singleton _).insert _) (insert_subset_iff.2 ⟨hs, singleton_subset_iff.2 ht⟩)
/-
**Filter.countableInter_ofCountableInter** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：countableInter_ofCountableInter (l : Set (Set α)) (hl : forall S : Set (Se
t α), S.Countable -> S subseteq l -> ⋂₀ S in l) (h_mono : forall s t, s in l -> 
s subseteq t -> t in l) : CountableInterFilter (Filter.ofCountableInter l hl h_m
ono)
参数：l : Set (Set α)；hl : forall S : Set (Set α), S.Countable -> S subseteq l -> ⋂
₀ S in l；h_mono : forall s t, s in l -> s subseteq t -> t in l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance countableInter_ofCountableInter (l : Set (Set α))
    (hl : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l)
    (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l) :
    CountableInterFilter (Filter.ofCountableInter l hl h_mono) :=
  ⟨hl⟩

@[simp]
/-
**Filter.mem_ofCountableInter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_ofCountableInter {l : Set (Set α)} (hl : forall S : Set (Set α), S.Cou
ntable -> S subseteq l -> ⋂₀ S in l) (h_mono : forall s t, s in l -> s subseteq 
t -> t in l) {s : Set α} : s in Filter.ofCountableInter l hl h_mono ↔ s in l
参数：Set α；hl : forall S : Set (Set α), S.Countable -> S subseteq l -> ⋂₀ S in l；h
_mono : forall s t, s in l -> s subseteq t -> t in l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ofCountableInter {l : Set (Set α)}
    (hl : ∀ S : Set (Set α), S.Countable → S ⊆ l → ⋂₀ S ∈ l) (h_mono : ∀ s t, s ∈ l → s ⊆ t → t ∈ l)
    {s : Set α} : s ∈ Filter.ofCountableInter l hl h_mono ↔ s ∈ l :=
  Iff.rfl

/-- Construct a filter with countable intersection property.
Similarly to `Filter.comk`, a set belongs to this filter if its complement satisfies the property.
Similarly to `Filter.ofCountableInter`,
this constructor deduces some properties from the countable intersection property
which becomes the countable union property because we take complements of all sets. -/
/-
**Filter.ofCountableUnion** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：ofCountableUnion (l : Set (Set α)) (hUnion : forall S : Set (Set α), S.Cou
ntable -> (forall s in S, s in l) -> ⋃₀ S in l) (hmono : forall t in l, forall s
 subseteq t, s in l) : Filter α
参数：l : Set (Set α)；hUnion : forall S : Set (Set α), S.Countable -> (forall s in 
S, s in l) -> ⋃₀ S in l；hmono : forall t in l, forall s subseteq t, s in l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a filter with countable intersection property.
Similarly to `Filter.comk`, a set belongs to this filter if its complement satis
fies the property.
Similarly to `Filter.ofCountableInter`,
this constructor deduces some properties from the countable intersection propert
y
which becomes the countable union property because we take complements of all se
ts.
-/
def ofCountableUnion (l : Set (Set α))
    (hUnion : ∀ S : Set (Set α), S.Countable → (∀ s ∈ S, s ∈ l) → ⋃₀ S ∈ l)
    (hmono : ∀ t ∈ l, ∀ s ⊆ t, s ∈ l) : Filter α := by
  refine .ofCountableInter {s | sᶜ ∈ l} (fun S hSc hSp ↦ ?_) fun s t ht hsub ↦ ?_
  · rw [mem_ofPred_eq, compl_sInter]
    apply hUnion (compl '' S) (hSc.image _)
    intro s hs
    rw [mem_image] at hs
    rcases hs with ⟨t, ht, rfl⟩
    apply hSp ht
  · rw [mem_ofPred_eq]
    rw [← compl_subset_compl] at hsub
    exact hmono sᶜ ht tᶜ hsub
/-
**Filter.countableInter_ofCountableUnion** 是 Mathlib 中的一个实例，位于命名空间 `Filter`。
形式化陈述：countableInter_ofCountableUnion (l : Set (Set α)) (h₁ h₂) : CountableInter
Filter (Filter.ofCountableUnion l h₁ h₂)
参数：l : Set (Set α)；h₁ h₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance countableInter_ofCountableUnion (l : Set (Set α)) (h₁ h₂) :
    CountableInterFilter (Filter.ofCountableUnion l h₁ h₂) :=
  countableInter_ofCountableInter ..

@[simp]
/-
**Filter.mem_ofCountableUnion** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_ofCountableUnion {l : Set (Set α)} {hunion hmono s} : s in ofCountable
Union l hunion hmono ↔ sᶜ in l
参数：Set α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ofCountableUnion {l : Set (Set α)} {hunion hmono s} :
    s ∈ ofCountableUnion l hunion hmono ↔ sᶜ ∈ l :=
  Iff.rfl

end Filter

/-
**countableInterFilter_principal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：countableInterFilter_principal (s : Set α) : CountableInterFilter (𝓟 s)
参数：s : Set α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_sInter`：subset_sInter {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t subseteq t') : t subseteq ⋂₀ S
-/
instance countableInterFilter_principal (s : Set α) : CountableInterFilter (𝓟 s) :=
  ⟨fun _ _ hS => subset_sInter hS⟩
/-
**countableInterFilter_bot** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：countableInterFilter_bot : CountableInterFilter (⊥ : Filter α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_empty`：principal_empty : 𝓟 (∅ : Set α) = ⊥
-/
instance countableInterFilter_bot : CountableInterFilter (⊥ : Filter α) := by
  rw [← principal_empty]
  apply countableInterFilter_principal
/-
**countableInterFilter_top** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：countableInterFilter_top : CountableInterFilter (⊤ : Filter α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.principal_univ`：∀ {α : Type u}, Filter.principal Set.univ = ⊤
-/
instance countableInterFilter_top : CountableInterFilter (⊤ : Filter α) := by
  rw [← principal_univ]
  apply countableInterFilter_principal
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (l : Filter β) [CountableInterFilter l] (f : α → β) :
    CountableInterFilter (comap f l) := by
  refine ⟨fun S hSc hS => ?_⟩
  choose! t htl ht using hS
  have : (⋂ s ∈ S, t s) ∈ l := (countable_bInter_mem hSc).2 htl
  refine ⟨_, this, ?_⟩
  simpa [preimage_iInter] using iInter₂_mono ht
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (l : Filter α) [CountableInterFilter l] (f : α → β) : CountableInterFilter (map f l) := by
  refine ⟨fun S hSc hS => ?_⟩
  simp only [mem_map, sInter_eq_biInter, preimage_iInter₂] at hS ⊢
  exact (countable_bInter_mem hSc).2 hS

/-- Infimum of two `CountableInterFilter`s is a `CountableInterFilter`. This is useful, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`. -/
/-
**countableInterFilter_inf** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：countableInterFilter_inf (l₁ l₂ : Filter α) [CountableInterFilter l₁] [Cou
ntableInterFilter l₂] : CountableInterFilter (l₁ ⊓ l₂)
参数：l₁ l₂ : Filter α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `countable_bInter_mem`：countable_bInter_mem {ι : Type*} {S : Set ι} (hS :
 S.Countable) {s : forall i in S, Set α} : (⋂ i, ⋂ hi : i in S, s i ‹_›) in l ↔ 
forall i, …
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
Infimum of two `CountableInterFilter`s is a `CountableInterFilter`. This is usef
ul, e.g.,
to automatically get an instance for `residual α ⊓ 𝓟 s`.
-/
instance countableInterFilter_inf (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊓ l₂) := by
  refine ⟨fun S hSc hS => ?_⟩
  choose s hs t ht hst using hS
  replace hs : (⋂ i ∈ S, s i ‹_›) ∈ l₁ := (countable_bInter_mem hSc).2 hs
  replace ht : (⋂ i ∈ S, t i ‹_›) ∈ l₂ := (countable_bInter_mem hSc).2 ht
  refine mem_of_superset (inter_mem_inf hs ht) (subset_sInter fun i hi => ?_)
  rw [hst i hi]
  apply inter_subset_inter <;> exact iInter_subset_of_subset i (iInter_subset _ _)

/-- Supremum of two `CountableInterFilter`s is a `CountableInterFilter`. -/
/-
**countableInterFilter_sup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：countableInterFilter_sup (l₁ l₂ : Filter α) [CountableInterFilter l₁] [Cou
ntableInterFilter l₂] : CountableInterFilter (l₁ ⊔ l₂)
参数：l₁ l₂ : Filter α。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `countable_sInter_mem`：countable_sInter_mem {S : Set (Set α)} (hSc : S.Co
untable) : ⋂₀ S in l ↔ forall s in S, s in l
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Supremum of two `CountableInterFilter`s is a `CountableInterFilter`.
-/
instance countableInterFilter_sup (l₁ l₂ : Filter α) [CountableInterFilter l₁]
    [CountableInterFilter l₂] : CountableInterFilter (l₁ ⊔ l₂) := by
  refine ⟨fun S hSc hS => ⟨?_, ?_⟩⟩ <;> refine (countable_sInter_mem hSc).2 fun s hs => ?_
  exacts [(hS s hs).1, (hS s hs).2]
/-
**CountableInterFilter.curry** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：CountableInterFilter.curry {α β : Type*} {l : Filter α} {m : Filter β} [Co
untableInterFilter l] [CountableInterFilter m] : CountableInterFilter (l.curry m
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eventually_countable_ball`：eventually_countable_ball {ι : Type*} {S : Se
t ι} (hS : S.Countable) {p : α -> forall i in S, Prop} : (forallᶠ x in l, forall
 i hi, p x i hi…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
instance CountableInterFilter.curry {α β : Type*} {l : Filter α} {m : Filter β}
    [CountableInterFilter l] [CountableInterFilter m] : CountableInterFilter (l.curry m) := ⟨by
  intro S Sct hS
  simp_rw [mem_curry_iff, mem_sInter, eventually_countable_ball (p := fun _ _ _ => (_, _) ∈ _) Sct,
    eventually_countable_ball (p := fun _ _ _ => ∀ᶠ (_ : β) in m, _)  Sct, ← mem_curry_iff]
  exact hS⟩

namespace Filter

variable (g : Set (Set α))

/-- `Filter.CountableGenerateSets g` is the (sets of the)
greatest `countableInterFilter` containing `g`. -/
/-
**Filter.CountableGenerateSets** 是 Mathlib 中的一个归纳类型，位于命名空间 `Filter`。
形式化陈述：{α : Type u_2} → Set (Set α) → Set α → Prop
参数：Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Filter.CountableGenerateSets g` is the (sets of the)
greatest `countableInterFilter` containing `g`.
-/
inductive CountableGenerateSets : Set α → Prop
  | basic {s : Set α} : s ∈ g → CountableGenerateSets s
  | univ : CountableGenerateSets univ
  | superset {s t : Set α} : CountableGenerateSets s → s ⊆ t → CountableGenerateSets t
  | sInter {S : Set (Set α)} :
    S.Countable → (∀ s ∈ S, CountableGenerateSets s) → CountableGenerateSets (⋂₀ S)

set_option backward.isDefEq.respectTransparency false in
/-- `Filter.countableGenerate g` is the greatest `countableInterFilter` containing `g`. -/
/-
**Filter.countableGenerate** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：countableGenerate : Filter α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Filter.countableGenerate g` is the greatest `countableInterFilter` containing `
g`.
-/
def countableGenerate : Filter α :=
  ofCountableInter {s | CountableGenerateSets g s} (fun _ ↦ .sInter) fun _ _ ↦ .superset
deriving CountableInterFilter

variable {g}

/-- A set is in the `countableInterFilter` generated by `g` if and only if
it contains a countable intersection of elements of `g`. -/
/-
**Filter.mem_countableGenerate_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：mem_countableGenerate_iff {s : Set α} : s in countableGenerate g ↔ exists 
S : Set (Set α), S subseteq g ∧ S.Countable ∧ ⋂₀ S subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.sInter_singleton`：sInter_singleton (s : Set α) : ⋂₀ {s} = s
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.Countable.biUnion`：∀ {α : Type u} {β : Type v} {s : Set α} {t : (a :
 α) → a ∈ s → Set β},   s.Countable → (∀ (a : α) (ha : a ∈ s), (t a ha).Countabl
e) → (⋃ a, …
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
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `countable_sInter_mem`：countable_sInter_mem {S : Set (Set α)} (hSc : S.Co
untable) : ⋂₀ S in l ↔ forall s in S, s in l
· 使用定理 `Filter.instCountableInterFilterCountableGenerate`：∀ {α : Type u_1} (g : 
Set (Set α)), CountableInterFilter (Filter.countableGenerate g)

--- 原说明 ---
A set is in the `countableInterFilter` generated by `g` if and only if
it contains a countable intersection of elements of `g`.
-/
theorem mem_countableGenerate_iff {s : Set α} :
    s ∈ countableGenerate g ↔ ∃ S : Set (Set α), S ⊆ g ∧ S.Countable ∧ ⋂₀ S ⊆ s := by
  constructor <;> intro h
  · induction h with
    | @basic s hs => exact ⟨{s}, by simp [hs]⟩
    | univ => exact ⟨∅, by simp⟩
    | superset _ _ ih => refine Exists.imp (fun S => ?_) ih; tauto
    | @sInter S Sct _ ih =>
      choose T Tg Tct hT using ih
      refine ⟨⋃ (s) (H : s ∈ S), T s H, by simpa, Sct.biUnion Tct, ?_⟩
      apply subset_sInter
      intro s H
      exact subset_trans (sInter_subset_sInter (subset_iUnion₂ s H)) (hT s H)
  rcases h with ⟨S, Sg, Sct, hS⟩
  refine mem_of_superset ((countable_sInter_mem Sct).mpr ?_) hS
  intro s H
  exact CountableGenerateSets.basic (Sg H)
/-
**Filter.le_countableGenerate_iff_of_countableInterFilter** 是 Mathlib 中的一个定理，位于命
名空间 `Filter`。
形式化陈述：le_countableGenerate_iff_of_countableInterFilter {f : Filter α} [Countable
InterFilter f] : f <= countableGenerate g ↔ g subseteq f.sets
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_trans`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preor
der α] {a b c : α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `countable_sInter_mem`：countable_sInter_mem {S : Set (Set α)} (hSc : S.Co
untable) : ⋂₀ S in l ↔ forall s in S, s in l
-/
theorem le_countableGenerate_iff_of_countableInterFilter {f : Filter α} [CountableInterFilter f] :
    f ≤ countableGenerate g ↔ g ⊆ f.sets := by
  constructor <;> intro h
  · exact subset_trans (fun s => CountableGenerateSets.basic) h
  intro s hs
  induction hs with
  | basic hs => exact h hs
  | univ => exact univ_mem
  | superset _ st ih => exact mem_of_superset ih st
  | sInter Sct _ ih => exact (countable_sInter_mem Sct).mpr ih

variable (g)

/-- `countableGenerate g` is the greatest `countableInterFilter` containing `g`. -/
/-
**Filter.countableGenerate_isGreatest** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：countableGenerate_isGreatest : IsGreatest { f : Filter α | CountableInterF
ilter f ∧ g subseteq f.sets } (countableGenerate g)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.instCountableInterFilterCountableGenerate`：∀ {α : Type u_1} (g : 
Set (Set α)), CountableInterFilter (Filter.countableGenerate g)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_countableGenerate_iff_of_countableInterFilter`：le_countableGen
erate_iff_of_countableInterFilter {f : Filter α} [CountableInterFilter f] : f <=
 countableGenerate g ↔ g subseteq f.sets

--- 原说明 ---
`countableGenerate g` is the greatest `countableInterFilter` containing `g`.
-/
theorem countableGenerate_isGreatest :
    IsGreatest { f : Filter α | CountableInterFilter f ∧ g ⊆ f.sets } (countableGenerate g) := by
  refine ⟨⟨inferInstance, fun s => CountableGenerateSets.basic⟩, ?_⟩
  rintro f ⟨fct, hf⟩
  rwa [@le_countableGenerate_iff_of_countableInterFilter _ _ _ fct]

end Filter

