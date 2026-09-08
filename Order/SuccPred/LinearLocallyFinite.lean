/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Countable.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.SuccPred.Archimedean

/-!
# Linear locally finite orders

We prove that a `LinearOrder` which is a `LocallyFiniteOrder` also verifies
* `SuccOrder`
* `PredOrder`
* `IsSuccArchimedean`
* `IsPredArchimedean`
* `Countable`

Furthermore, we show that there is an `OrderIso` between such an order and a subset of `ℤ`.

## Main definitions

* `toZ i0 i`: in a linear order on which we can define predecessors and successors and which is
  succ-archimedean, we can assign a unique integer `toZ i0 i` to each element `i : ι` while
  respecting the order, starting from `toZ i0 i0 = 0`.

## Main results

Results about linear locally finite orders:
* `LinearLocallyFiniteOrder.SuccOrder`: a linear locally finite order has a successor function.
* `LinearLocallyFiniteOrder.PredOrder`: a linear locally finite order has a predecessor
  function.
* `LinearLocallyFiniteOrder.isSuccArchimedean`: a linear locally finite order is
  succ-archimedean.
* `LinearOrder.pred_archimedean_of_succ_archimedean`: a succ-archimedean linear order is also
  pred-archimedean.
* `countable_of_linear_succ_pred_arch` : a succ-archimedean linear order is countable.

About `toZ`:
* `orderIsoRangeToZOfLinearSuccPredArch`: `toZ` defines an `OrderIso` between `ι` and its
  range.
* `orderIsoNatOfLinearSuccPredArch`: if the order has a bot but no top, `toZ` defines an
  `OrderIso` between `ι` and `ℕ`.
* `orderIsoIntOfLinearSuccPredArch`: if the order has neither bot nor top, `toZ` defines an
  `OrderIso` between `ι` and `ℤ`.
* `orderIsoRangeOfLinearSuccPredArch`: if the order has both a bot and a top, `toZ` gives an
  `OrderIso` between `ι` and `Finset.range ((toZ ⊥ ⊤).toNat + 1)`.

-/

public section

open Order

variable {ι : Type*} [LinearOrder ι]

namespace LinearOrder

variable [SuccOrder ι] [PredOrder ι]

/-
**LinearOrder.** 是 Mathlib 中的一个实例，位于命名空间 `LinearOrder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) isPredArchimedean_of_isSuccArchimedean [IsSuccArchimedean ι] :
    IsPredArchimedean ι where
  exists_pred_iterate_of_le {i j} hij := by
    have h_exists := exists_succ_iterate_of_le hij
    obtain ⟨n, hn_eq, hn_lt_ne⟩ : ∃ n, succ^[n] i = j ∧ ∀ m < n, succ^[m] i ≠ j :=
      ⟨Nat.find h_exists, Nat.find_spec h_exists, fun m hmn ↦ Nat.find_min h_exists hmn⟩
    refine ⟨n, ?_⟩
    rw [← hn_eq]
    cases n with
    | zero => simp only [Function.iterate_zero, id]
    | succ n =>
      rw [pred_succ_iterate_of_not_isMax]
      rw [Nat.succ_sub_succ_eq_sub, tsub_zero]
      suffices succ^[n] i < succ^[n.succ] i from not_isMax_of_lt this
      refine lt_of_le_of_ne ?_ ?_
      · rw [Function.iterate_succ_apply']
        exact le_succ _
      · rw [hn_eq]
        exact hn_lt_ne _ (Nat.lt_succ_self n)
/-
**LinearOrder.isSuccArchimedean_of_isPredArchimedean** 是 Mathlib 中的一个实例，位于命名空间 `
LinearOrder`。
形式化陈述：isSuccArchimedean_of_isPredArchimedean [IsPredArchimedean ι] : IsSuccArchi
medean ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isSuccArchimedean_of_isPredArchimedean [IsPredArchimedean ι] : IsSuccArchimedean ι :=
  inferInstanceAs (IsSuccArchimedean ιᵒᵈᵒᵈ)

/-- In a linear `SuccOrder` that's also a `PredOrder`, `IsSuccArchimedean` and `IsPredArchimedean`
are equivalent. -/
/-
**LinearOrder.isSuccArchimedean_iff_isPredArchimedean** 是 Mathlib 中的一个定理，位于命名空间 
`LinearOrder`。
形式化陈述：isSuccArchimedean_iff_isPredArchimedean : IsSuccArchimedean ι ↔ IsPredArch
imedean ι where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearOrder.isPredArchimedean_of_isSuccArchimedean`：∀ {ι : Type u_1} [in
st : LinearOrder ι] [inst_1 : SuccOrder ι] [inst_2 : PredOrder ι] [IsSuccArchime
dean ι],   IsPredArchimedean ι

--- 原说明 ---
In a linear `SuccOrder` that's also a `PredOrder`, `IsSuccArchimedean` and `IsPr
edArchimedean`
are equivalent.
-/
theorem isSuccArchimedean_iff_isPredArchimedean : IsSuccArchimedean ι ↔ IsPredArchimedean ι where
  mp _ := isPredArchimedean_of_isSuccArchimedean
  mpr _ := isSuccArchimedean_of_isPredArchimedean

end LinearOrder

namespace LinearLocallyFiniteOrder

/-- Successor in a linear order. This defines a true successor only when `i` is isolated from above,
i.e. when `i` is not the greatest lower bound of `(i, ∞)`. -/
/-
**LinearLocallyFiniteOrder.succFn** 是 Mathlib 中的一个定义，位于命名空间 `LinearLocallyFinite
Order`。
形式化陈述：succFn (i : ι) : ι
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `exists_glb_Ioi`：∀ {γ : Type u_3} [inst : LinearOrder γ] (i : γ), ∃ j, Is
GLB (Set.Ioi i) j

--- 原说明 ---
Successor in a linear order. This defines a true successor only when `i` is isol
ated from above,
i.e. when `i` is not the greatest lower bound of `(i, ∞)`.
-/
noncomputable def succFn (i : ι) : ι :=
  (exists_glb_Ioi i).choose
/-
**LinearLocallyFiniteOrder.succFn_spec** 是 Mathlib 中的一个定理，位于命名空间 `LinearLocallyF
initeOrder`。
形式化陈述：succFn_spec (i : ι) : IsGLB (Set.Ioi i) (succFn i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `exists_glb_Ioi`：∀ {γ : Type u_3} [inst : LinearOrder γ] (i : γ), ∃ j, Is
GLB (Set.Ioi i) j
-/
theorem succFn_spec (i : ι) : IsGLB (Set.Ioi i) (succFn i) :=
  (exists_glb_Ioi i).choose_spec
/-
**LinearLocallyFiniteOrder.le_succFn** 是 Mathlib 中的一个定理，位于命名空间 `LinearLocallyFin
iteOrder`。
形式化陈述：le_succFn (i : ι) : i <= succFn i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_isGLB_iff`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a b : α}
, IsGLB s a → (b ≤ a ↔ b ∈ lowerBounds s)
· 使用定理 `LinearLocallyFiniteOrder.succFn_spec`：succFn_spec (i : ι) : IsGLB (Set.I
oi i) (succFn i)
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem le_succFn (i : ι) : i ≤ succFn i := by
  rw [le_isGLB_iff (succFn_spec i), mem_lowerBounds]
  exact fun x hx ↦ le_of_lt hx
/-
**LinearLocallyFiniteOrder.isGLB_Ioc_of_isGLB_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earLocallyFiniteOrder`。
形式化陈述：isGLB_Ioc_of_isGLB_Ioi {i j k : ι} (hij_lt : i < j) (h : IsGLB (Set.Ioi i)
 k) : IsGLB (Set.Ioc i j) k
参数：hij_lt : i < j；h : IsGLB (Set.Ioi i) k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem isGLB_Ioc_of_isGLB_Ioi {i j k : ι} (hij_lt : i < j) (h : IsGLB (Set.Ioi i) k) :
    IsGLB (Set.Ioc i j) k := by
  simp_rw [IsGLB, IsGreatest, mem_upperBounds, mem_lowerBounds] at h ⊢
  refine ⟨fun x hx ↦ h.1 x hx.1, fun x hx ↦ h.2 x ?_⟩
  intro y hy
  rcases le_or_gt y j with h_le | h_lt
  · exact hx y ⟨hy, h_le⟩
  · exact le_trans (hx j ⟨hij_lt, le_rfl⟩) h_lt.le
/-
**LinearLocallyFiniteOrder.isMax_of_succFn_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearL
ocallyFiniteOrder`。
形式化陈述：isMax_of_succFn_le [LocallyFiniteOrder ι] (i : ι) (hi : succFn i <= i) : I
sMax i
参数：i : ι；hi : succFn i <= i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearLocallyFiniteOrder.le_succFn`：le_succFn (i : ι) : i <= succFn i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_Ioc`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : LocallyFi
niteOrder α] (b a : α), ↑(Finset.Ioc b a) = Set.Ioc b a
· 使用定理 `LinearLocallyFiniteOrder.succFn_spec`：succFn_spec (i : ι) : IsGLB (Set.I
oi i) (succFn i)
· 使用定理 `LinearLocallyFiniteOrder.isGLB_Ioc_of_isGLB_Ioi`：isGLB_Ioc_of_isGLB_Ioi 
{i j k : ι} (hij_lt : i < j) (h : IsGLB (Set.Ioi i) k) : IsGLB (Set.Ioc i j) k
· 使用定理 `Finset.isGLB_mem`：isGLB_mem [LinearOrder α] {i : α} (s : Finset α) (his 
: IsGLB (s : Set α) i) (hs : s.Nonempty) : i in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Ioc`：mem_Ioc : x in Ioc a b ↔ a < x ∧ x <= b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem isMax_of_succFn_le [LocallyFiniteOrder ι] (i : ι) (hi : succFn i ≤ i) : IsMax i := by
  refine fun j _ ↦ not_lt.mp fun hij_lt ↦ ?_
  have h_succFn_eq : succFn i = i := le_antisymm hi (le_succFn i)
  have h_glb : IsGLB (Finset.Ioc i j : Set ι) i := by
    rw [Finset.coe_Ioc]
    have h := succFn_spec i
    rw [h_succFn_eq] at h
    exact isGLB_Ioc_of_isGLB_Ioi hij_lt h
  have hi_mem : i ∈ Finset.Ioc i j := by
    refine Finset.isGLB_mem _ h_glb ?_
    exact ⟨_, Finset.mem_Ioc.mpr ⟨hij_lt, le_rfl⟩⟩
  rw [Finset.mem_Ioc] at hi_mem
  exact lt_irrefl i hi_mem.1
/-
**LinearLocallyFiniteOrder.succFn_le_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `LinearLoca
llyFiniteOrder`。
形式化陈述：succFn_le_of_lt (i j : ι) (hij : i < j) : succFn i <= j
参数：i j : ι；hij : i < j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearLocallyFiniteOrder.succFn_spec`：succFn_spec (i : ι) : IsGLB (Set.I
oi i) (succFn i)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x
· 使用定理 `IsGreatest.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α) (a : α), IsG
reatest s a = (a ∈ s ∧ a ∈ upperBounds s)
· 使用定理 `IsGLB.eq_1`：∀ {α : Type u_1} [inst : LE α] (s : Set α), IsGLB s = IsGrea
test (lowerBounds s)
-/
theorem succFn_le_of_lt (i j : ι) (hij : i < j) : succFn i ≤ j := by
  have h := succFn_spec i
  rw [IsGLB, IsGreatest, mem_lowerBounds] at h
  exact h.1 j hij
/-
**LinearLocallyFiniteOrder.le_of_lt_succFn** 是 Mathlib 中的一个定理，位于命名空间 `LinearLoca
llyFiniteOrder`。
形式化陈述：le_of_lt_succFn (j i : ι) (hij : j < succFn i) : j <= i
参数：j i : ι；hij : j < succFn i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_isGLB_iff`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a b : α}
, IsGLB s a → (b < a ↔ ∃ c ∈ lowerBounds s, b < c)
· 使用定理 `LinearLocallyFiniteOrder.succFn_spec`：succFn_spec (i : ι) : IsGLB (Set.I
oi i) (succFn i)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x
-/
theorem le_of_lt_succFn (j i : ι) (hij : j < succFn i) : j ≤ i := by
  rw [lt_isGLB_iff (succFn_spec i)] at hij
  obtain ⟨k, hk_lb, hk⟩ := hij
  rw [mem_lowerBounds] at hk_lb
  exact not_lt.mp fun hi_lt_j ↦ not_le.mpr hk (hk_lb j hi_lt_j)

variable (ι) in
/-- A locally finite order is a `SuccOrder`.
This is not an instance, because its `succ` field conflicts with computable `SuccOrder` structures
on `ℕ` and `ℤ`. -/
@[instance_reducible]
/-
**LinearLocallyFiniteOrder.succOrder** 是 Mathlib 中的一个定义，位于命名空间 `LinearLocallyFin
iteOrder`。
形式化陈述：succOrder [LocallyFiniteOrder ι] : SuccOrder ι where succ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearLocallyFiniteOrder.le_succFn`：le_succFn (i : ι) : i <= succFn i
· 使用定理 `LinearLocallyFiniteOrder.isMax_of_succFn_le`：isMax_of_succFn_le [Locally
FiniteOrder ι] (i : ι) (hi : succFn i <= i) : IsMax i
· 使用定理 `LinearLocallyFiniteOrder.succFn_le_of_lt`：succFn_le_of_lt (i j : ι) (hij
 : i < j) : succFn i <= j

--- 原说明 ---
A locally finite order is a `SuccOrder`.
This is not an instance, because its `succ` field conflicts with computable `Suc
cOrder` structures
on `ℕ` and `ℤ`.
-/
noncomputable def succOrder [LocallyFiniteOrder ι] : SuccOrder ι where
  succ := succFn
  le_succ := le_succFn
  max_of_succ_le h := isMax_of_succFn_le _ h
  succ_le_of_lt h := succFn_le_of_lt _ _ h

variable (ι) in
/-- A locally finite order is a `PredOrder`.
This is not an instance, because its `succ` field conflicts with computable `PredOrder` structures
on `ℕ` and `ℤ`. -/
@[instance_reducible]
/-
**LinearLocallyFiniteOrder.predOrder** 是 Mathlib 中的一个定义，位于命名空间 `LinearLocallyFin
iteOrder`。
形式化陈述：predOrder [LocallyFiniteOrder ι] : PredOrder ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A locally finite order is a `PredOrder`.
This is not an instance, because its `succ` field conflicts with computable `Pre
dOrder` structures
on `ℕ` and `ℤ`.
-/
noncomputable def predOrder [LocallyFiniteOrder ι] : PredOrder ι :=
  letI := succOrder (ι := ιᵒᵈ)
  inferInstanceAs (PredOrder ιᵒᵈᵒᵈ)
/-
**LinearLocallyFiniteOrder.** 是 Mathlib 中的一个实例，位于命名空间 `LinearLocallyFiniteOrder`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [LocallyFiniteOrder ι] [SuccOrder ι] : IsSuccArchimedean ι where
  exists_succ_iterate_of_le := by
    intro i j hij
    rw [le_iff_lt_or_eq] at hij
    rcases hij with hij | hij
    swap
    · refine ⟨0, ?_⟩
      simpa only [Function.iterate_zero, id] using hij
    by_contra! h
    have h_lt : ∀ n, succ^[n] i < j := fun n ↦ by
      induction n with
      | zero => simpa only [Function.iterate_zero, id] using hij
      | succ n hn =>
        refine lt_of_le_of_ne ?_ (h _)
        rw [Function.iterate_succ', Function.comp_apply]
        exact succ_le_of_lt hn
    have h_mem : ∀ n, succ^[n] i ∈ Finset.Icc i j :=
      fun n ↦ Finset.mem_Icc.mpr ⟨le_succ_iterate n i, (h_lt n).le⟩
    obtain ⟨n, m, hnm, h_eq⟩ : ∃ n m, n < m ∧ succ^[n] i = succ^[m] i := by
      let f : ℕ → Finset.Icc i j := fun n ↦ ⟨succ^[n] i, h_mem n⟩
      obtain ⟨n, m, hnm_ne, hfnm⟩ : ∃ n m, n ≠ m ∧ f n = f m :=
        Finite.exists_ne_map_eq_of_infinite f
      have hnm_eq : succ^[n] i = succ^[m] i := by simpa only [f, Subtype.mk_eq_mk] using hfnm
      rcases le_total n m with h_le | h_le
      · exact ⟨n, m, lt_of_le_of_ne h_le hnm_ne, hnm_eq⟩
      · exact ⟨m, n, lt_of_le_of_ne h_le hnm_ne.symm, hnm_eq.symm⟩
    have h_max : IsMax (succ^[n] i) := isMax_iterate_succ_of_eq_of_ne h_eq hnm.ne
    exact not_le.mpr (h_lt n) (h_max (h_lt n).le)
/-
**LinearLocallyFiniteOrder.** 是 Mathlib 中的一个实例，位于命名空间 `LinearLocallyFiniteOrder`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [LocallyFiniteOrder ι] [PredOrder ι] : IsPredArchimedean ι :=
  inferInstanceAs (IsPredArchimedean ιᵒᵈᵒᵈ)

end LinearLocallyFiniteOrder

section toZ

-- Requiring either of `IsSuccArchimedean` or `IsPredArchimedean` is equivalent.
variable [SuccOrder ι] [IsSuccArchimedean ι] [PredOrder ι] {i0 i : ι}

-- For "to_Z"

/-- `toZ` numbers elements of `ι` according to their order, starting from `i0`. We prove in
`orderIsoRangeToZOfLinearSuccPredArch` that this defines an `OrderIso` between `ι` and
the range of `toZ`. -/
/-
**toZ** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：toZ (i0 i : ι) : Int
参数：i0 i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toZ` numbers elements of `ι` according to their order, starting from `i0`. We p
rove in
`orderIsoRangeToZOfLinearSuccPredArch` that this defines an `OrderIso` between `
ι` and
the range of `toZ`.
-/
def toZ (i0 i : ι) : ℤ :=
  dite (i0 ≤ i) (fun hi ↦ Nat.find (exists_succ_iterate_of_le hi)) fun hi ↦
    -Nat.find (exists_pred_iterate_of_le (α := ι) (not_le.mp hi).le)
/-
**toZ_of_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_of_ge (hi : i0 <= i) : toZ i0 i = Nat.find (exists_succ_iterate_of_le 
hi)
参数：hi : i0 <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem toZ_of_ge (hi : i0 ≤ i) : toZ i0 i = Nat.find (exists_succ_iterate_of_le hi) :=
  dif_pos hi
/-
**toZ_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_of_lt (hi : i < i0) : toZ i0 i = -Nat.find (exists_pred_iterate_of_le 
(α
参数：hi : i < i0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
-/
theorem toZ_of_lt (hi : i < i0) :
    toZ i0 i = -Nat.find (exists_pred_iterate_of_le (α := ι) hi.le) :=
  dif_neg (not_le.mpr hi)

@[simp]
/-
**toZ_of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_of_eq : toZ i0 i0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toZ_of_ge`：toZ_of_ge (hi : i0 <= i) : toZ i0 i = Nat.find (exists_succ_i
terate_of_le hi)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `Nat.find_le`：find_le {h : exists n, p n} (hn : p n) : Nat.find h <= n
· 使用定理 `Function.iterate_zero`：iterate_zero : f^[0] = id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
-/
theorem toZ_of_eq : toZ i0 i0 = 0 := by
  rw [toZ_of_ge le_rfl]
  norm_cast
  rw [← nonpos_iff_eq_zero]
  apply Nat.find_le
  rw [Function.iterate_zero, id]
/-
**iterate_succ_toZ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterate_succ_toZ (i : ι) (hi : i0 <= i) : succ^[(toZ i0 i).toNat] i0 = i
参数：i : ι；hi : i0 <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toZ_of_ge`：toZ_of_ge (hi : i0 <= i) : toZ i0 i = Nat.find (exists_succ_i
terate_of_le hi)
· 使用定理 `Int.toNat_natCast`：∀ (n : ℕ), (↑n).toNat = n
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem iterate_succ_toZ (i : ι) (hi : i0 ≤ i) : succ^[(toZ i0 i).toNat] i0 = i := by
  rw [toZ_of_ge hi, Int.toNat_natCast]
  exact Nat.find_spec (exists_succ_iterate_of_le hi)
/-
**iterate_pred_toZ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iterate_pred_toZ (i : ι) (hi : i < i0) : pred^[(-toZ i0 i).toNat] i0 = i
参数：i : ι；hi : i < i0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPredArchimedean.exists_pred_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : PredOrder α} [self : IsPredArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.pred^[n] b = a
· 使用定理 `LinearOrder.isPredArchimedean_of_isSuccArchimedean`：∀ {ι : Type u_1} [in
st : LinearOrder ι] [inst_1 : SuccOrder ι] [inst_2 : PredOrder ι] [IsSuccArchime
dean ι],   IsPredArchimedean ι
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toZ_of_lt`：toZ_of_lt (hi : i < i0) : toZ i0 i = -Nat.find (exists_pred_i
terate_of_le (α
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.toNat_natCast`：∀ (n : ℕ), (↑n).toNat = n
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem iterate_pred_toZ (i : ι) (hi : i < i0) : pred^[(-toZ i0 i).toNat] i0 = i := by
  rw [toZ_of_lt hi, neg_neg, Int.toNat_natCast]
  exact Nat.find_spec (exists_pred_iterate_of_le hi.le)
/-
**toZ_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toZ_nonneg (hi : i0 <= i) : 0 <= toZ i0 i
参数：hi : i0 <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toZ_of_ge`：toZ_of_ge (hi : i0 <= i) : toZ i0 i = Nat.find (exists_succ_i
terate_of_le hi)
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
-/
lemma toZ_nonneg (hi : i0 ≤ i) : 0 ≤ toZ i0 i := by rw [toZ_of_ge hi]; exact Int.natCast_nonneg _
/-
**toZ_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_neg (hi : i < i0) : toZ i0 i < 0
参数：hi : i < i0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `IsPredArchimedean.exists_pred_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : PredOrder α} [self : IsPredArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.pred^[n] b = a
· 使用定理 `LinearOrder.isPredArchimedean_of_isSuccArchimedean`：∀ {ι : Type u_1} [in
st : LinearOrder ι] [inst_1 : SuccOrder ι] [inst_2 : PredOrder ι] [IsSuccArchime
dean ι],   IsPredArchimedean ι
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toZ_of_lt`：toZ_of_lt (hi : i < i0) : toZ i0 i = -Nat.find (exists_pred_i
terate_of_le (α
· 使用定理 `iterate_pred_toZ`：iterate_pred_toZ (i : ι) (hi : i < i0) : pred^[(-toZ i
0 i).toNat] i0 = i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toZ_neg (hi : i < i0) : toZ i0 i < 0 := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [toZ_of_lt hi]
    lia
  · by_contra h
    have h_eq := iterate_pred_toZ i hi
    rw [← h_eq, h] at hi
    simp only [neg_zero, Int.toNat_zero, Function.iterate_zero, id, lt_self_iff_false] at hi
/-
**toZ_iterate_succ_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_iterate_succ_le (n : Nat) : toZ i0 (succ^[n] i0) <= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
· 使用定理 `Order.le_succ_iterate`：le_succ_iterate (k : Nat) (x : α) : x <= succ^[k]
 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toZ_of_ge`：toZ_of_ge (hi : i0 <= i) : toZ i0 i = Nat.find (exists_succ_i
terate_of_le hi)
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
-/
theorem toZ_iterate_succ_le (n : ℕ) : toZ i0 (succ^[n] i0) ≤ n := by
  rw [toZ_of_ge (le_succ_iterate _ _)]
  norm_cast
  exact Nat.find_min' _ rfl
/-
**toZ_iterate_pred_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_iterate_pred_ge (n : Nat) : -(n : Int) <= toZ i0 (pred^[n] i0)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Order.pred_iterate_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pr
edOrder α] (k : ℕ) (x : α), Order.pred^[k] x ≤ x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toZ_of_eq`：toZ_of_eq : toZ i0 i0 = 0
· 使用定理 `IsPredArchimedean.exists_pred_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : PredOrder α} [self : IsPredArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.pred^[n] b = a
· 使用定理 `LinearOrder.isPredArchimedean_of_isSuccArchimedean`：∀ {ι : Type u_1} [in
st : LinearOrder ι] [inst_1 : SuccOrder ι] [inst_2 : PredOrder ι] [IsSuccArchime
dean ι],   IsPredArchimedean ι
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `toZ_of_lt`：toZ_of_lt (hi : i < i0) : toZ i0 i = -Nat.find (exists_pred_i
terate_of_le (α
· 使用定理 `Int.neg_le_neg`：∀ {a b : ℤ}, a ≤ b → -b ≤ -a
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
-/
theorem toZ_iterate_pred_ge (n : ℕ) : -(n : ℤ) ≤ toZ i0 (pred^[n] i0) := by
  rcases le_or_gt i0 (pred^[n] i0) with h | h
  · have h_eq : pred^[n] i0 = i0 := le_antisymm (pred_iterate_le _ _) h
    rw [h_eq, toZ_of_eq]
    lia
  · rw [toZ_of_lt h]
    refine Int.neg_le_neg ?_
    norm_cast
    exact Nat.find_min' _ rfl
/-
**toZ_iterate_succ_of_not_isMax** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_iterate_succ_of_not_isMax (n : Nat) (hn : ¬IsMax (succ^[n] i0)) : toZ 
i0 (succ^[n] i0) = n
参数：n : Nat；hn : ¬IsMax (succ^[n] i0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iterate_succ_toZ`：iterate_succ_toZ (i : ι) (hi : i0 <= i) : succ^[(toZ i
0 i).toNat] i0 = i
· 使用定理 `Order.le_succ_iterate`：le_succ_iterate (k : Nat) (x : α) : x <= succ^[k]
 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.toNat_eq_max`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `IsSuccArchimedean.exists_succ_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : SuccOrder α} [self : IsSuccArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.succ^[n] a = b
· 使用定理 `toZ_of_ge`：toZ_of_ge (hi : i0 <= i) : toZ i0 i = Nat.find (exists_succ_i
terate_of_le hi)
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Order.isMax_iterate_succ_of_eq_of_ne`：isMax_iterate_succ_of_eq_of_ne {n 
m : Nat} (h_eq : succ^[n] a = succ^[m] a) (h_ne : n != m) : IsMax (succ^[n] a)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem toZ_iterate_succ_of_not_isMax (n : ℕ) (hn : ¬IsMax (succ^[n] i0)) :
    toZ i0 (succ^[n] i0) = n := by
  let m := (toZ i0 (succ^[n] i0)).toNat
  have h_eq : succ^[m] i0 = succ^[n] i0 := iterate_succ_toZ _ (le_succ_iterate _ _)
  by_cases hmn : m = n
  · nth_rw 2 [← hmn]
    rw [Int.toNat_eq_max, toZ_of_ge (le_succ_iterate _ _), max_eq_left]
    exact Int.natCast_nonneg _
  suffices IsMax (succ^[n] i0) from absurd this hn
  exact isMax_iterate_succ_of_eq_of_ne h_eq.symm (Ne.symm hmn)
/-
**toZ_iterate_pred_of_not_isMin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_iterate_pred_of_not_isMin (n : Nat) (hn : ¬IsMin (pred^[n] i0)) : toZ 
i0 (pred^[n] i0) = -n
参数：n : Nat；hn : ¬IsMin (pred^[n] i0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `toZ_of_eq`：toZ_of_eq : toZ i0 i0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Order.pred_iterate_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pr
edOrder α] (k : ℕ) (x : α), Order.pred^[k] x ≤ x
· 使用定理 `Function.iterate_zero`：iterate_zero : f^[0] = id
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `Order.isMin_iterate_pred_of_eq_of_ne`：isMin_iterate_pred_of_eq_of_ne {n 
m : Nat} (h_eq : pred^[n] a = pred^[m] a) (h_ne : n != m) : IsMin (pred^[n] a)
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `iterate_pred_toZ`：iterate_pred_toZ (i : ι) (hi : i < i0) : pred^[(-toZ i
0 i).toNat] i0 = i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.toNat_eq_max`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `IsPredArchimedean.exists_pred_iterate_of_le`：∀ {α : Type u_3} {inst : Pr
eorder α} {inst_1 : PredOrder α} [self : IsPredArchimedean α] {a b : α},   a ≤ b
 → ∃ n, Order.pred^[n] b = a
· 使用定理 `LinearOrder.isPredArchimedean_of_isSuccArchimedean`：∀ {ι : Type u_1} [in
st : LinearOrder ι] [inst_1 : SuccOrder ι] [inst_2 : PredOrder ι] [IsSuccArchime
dean ι],   IsPredArchimedean ι
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `toZ_of_lt`：toZ_of_lt (hi : i < i0) : toZ i0 i = -Nat.find (exists_pred_i
terate_of_le (α
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Int.natCast_nonneg`：∀ (n : ℕ), 0 ≤ ↑n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem toZ_iterate_pred_of_not_isMin (n : ℕ) (hn : ¬IsMin (pred^[n] i0)) :
    toZ i0 (pred^[n] i0) = -n := by
  rcases n with - | n
  · simp
  have : pred^[n.succ] i0 < i0 := by
    refine lt_of_le_of_ne (pred_iterate_le _ _) fun h_pred_iterate_eq ↦ hn ?_
    have h_pred_eq_pred : pred^[n.succ] i0 = pred^[0] i0 := by
      rwa [Function.iterate_zero, id]
    exact isMin_iterate_pred_of_eq_of_ne h_pred_eq_pred (Nat.succ_ne_zero n)
  let m := (-toZ i0 (pred^[n.succ] i0)).toNat
  have h_eq : pred^[m] i0 = pred^[n.succ] i0 := iterate_pred_toZ _ this
  by_cases hmn : m = n + 1
  · nth_rw 2 [← hmn]
    rw [Int.toNat_eq_max, toZ_of_lt this, max_eq_left, neg_neg]
    rw [neg_neg]
    exact Int.natCast_nonneg _
  · suffices IsMin (pred^[n.succ] i0) from absurd this hn
    exact isMin_iterate_pred_of_eq_of_ne h_eq.symm (Ne.symm hmn)
/-
**toZ_strictMono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_strictMono : StrictMono (toZ i0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iterate_succ_toZ`：iterate_succ_toZ (i : ι) (hi : i0 <= i) : succ^[(toZ i
0 i).toNat] i0 = i
· 使用定理 `Monotone.monotone_iterate_of_le_map`：monotone_iterate_of_le_map (hf : Mo
notone f) (hx : x <= f x) : Monotone fun n => f^[n] x
· 使用定理 `Order.succ_mono`：succ_mono : Monotone (succ : α -> α)
· 使用定理 `Order.le_succ`：le_succ : forall a : α, a <= succ a
· 使用定理 `Int.toNat_le_toNat`：∀ {n m : ℤ}, n ≤ m → n.toNat ≤ m.toNat
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `toZ_neg`：toZ_neg (hi : i < i0) : toZ i0 i < 0
· 使用引理 `toZ_nonneg`：toZ_nonneg (hi : i0 <= i) : 0 <= toZ i0 i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `iterate_pred_toZ`：iterate_pred_toZ (i : ι) (hi : i < i0) : pred^[(-toZ i
0 i).toNat] i0 = i
· 使用定理 `Monotone.antitone_iterate_of_map_le`：antitone_iterate_of_map_le (hf : Mo
notone f) (hx : f x <= x) : Antitone fun n => f^[n] x
· 使用定理 `Order.pred_mono`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrde
r α], Monotone Order.pred
· 使用定理 `Order.pred_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : PredOrder 
α] (a : α), Order.pred a ≤ a
· 使用定理 `Int.neg_le_neg`：∀ {a b : ℤ}, a ≤ b → -b ≤ -a
-/
theorem toZ_strictMono : StrictMono (toZ i0) := by
  intro j i h_le
  contrapose! h_le
  rcases le_or_gt i0 i with hi | hi <;> rcases le_or_gt i0 j with hj | hj
  · rw [← iterate_succ_toZ i hi, ← iterate_succ_toZ j hj]
    exact Monotone.monotone_iterate_of_le_map succ_mono (le_succ _) (Int.toNat_le_toNat h_le)
  · exact absurd ((toZ_neg hj).trans_le (toZ_nonneg hi)) (not_lt.mpr h_le)
  · exact hi.le.trans hj
  · rw [← iterate_pred_toZ i hi, ← iterate_pred_toZ j hj]
    refine Monotone.antitone_iterate_of_map_le pred_mono (pred_le _) (Int.toNat_le_toNat ?_)
    exact Int.neg_le_neg h_le
/-
**injective_toZ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_toZ : Function.Injective (toZ i0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `toZ_strictMono`：toZ_strictMono : StrictMono (toZ i0)
-/
theorem injective_toZ : Function.Injective (toZ i0) :=
  toZ_strictMono.injective

@[simp]
/-
**toZ_le_toZ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_le_toZ {i j : ι} : toZ i0 i <= toZ i0 j ↔ i <= j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `toZ_strictMono`：toZ_strictMono : StrictMono (toZ i0)
-/
theorem toZ_le_toZ {i j : ι} : toZ i0 i ≤ toZ i0 j ↔ i ≤ j :=
  toZ_strictMono.le_iff_le

@[deprecated (since := "2026-05-07")]
alias toZ_le_iff := toZ_le_toZ

@[deprecated toZ_le_toZ (since := "2026-05-06")]
alias ⟨le_of_toZ_le, toZ_mono⟩ := toZ_le_toZ

@[simp]
/-
**toZ_lt_toZ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_lt_toZ {i j : ι} : toZ i0 i < toZ i0 j ↔ i < j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `toZ_strictMono`：toZ_strictMono : StrictMono (toZ i0)
-/
theorem toZ_lt_toZ {i j : ι} : toZ i0 i < toZ i0 j ↔ i < j :=
  toZ_strictMono.lt_iff_lt

@[deprecated (since := "2026-05-07")]
alias toZ_lt_iff := toZ_lt_toZ

@[simp]
/-
**toZ_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_inj {i j : ι} : toZ i0 i = toZ i0 j ↔ i = j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `injective_toZ`：injective_toZ : Function.Injective (toZ i0)
-/
theorem toZ_inj {i j : ι} : toZ i0 i = toZ i0 j ↔ i = j :=
  injective_toZ.eq_iff
/-
**toZ_iterate_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_iterate_succ [NoMaxOrder ι] (n : Nat) : toZ i0 (succ^[n] i0) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toZ_iterate_succ_of_not_isMax`：toZ_iterate_succ_of_not_isMax (n : Nat) (
hn : ¬IsMax (succ^[n] i0)) : toZ i0 (succ^[n] i0) = n
· 使用定理 `not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxOrder α] (a : α), 
¬IsMax a
-/
theorem toZ_iterate_succ [NoMaxOrder ι] (n : ℕ) : toZ i0 (succ^[n] i0) = n :=
  toZ_iterate_succ_of_not_isMax n (not_isMax _)
/-
**toZ_iterate_pred** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toZ_iterate_pred [NoMinOrder ι] (n : Nat) : toZ i0 (pred^[n] i0) = -n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `toZ_iterate_pred_of_not_isMin`：toZ_iterate_pred_of_not_isMin (n : Nat) (
hn : ¬IsMin (pred^[n] i0)) : toZ i0 (pred^[n] i0) = -n
· 使用定理 `not_isMin`：not_isMin [NoMinOrder α] (a : α) : ¬IsMin a
-/
theorem toZ_iterate_pred [NoMinOrder ι] (n : ℕ) : toZ i0 (pred^[n] i0) = -n :=
  toZ_iterate_pred_of_not_isMin n (not_isMin _)

end toZ

section OrderIso

variable [SuccOrder ι] [PredOrder ι] [IsSuccArchimedean ι]

set_option backward.isDefEq.respectTransparency.types false in
/-- `toZ` defines an `OrderIso` between `ι` and its range. -/
/-
**orderIsoRangeToZOfLinearSuccPredArch** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：orderIsoRangeToZOfLinearSuccPredArch [hι : Nonempty ι] : ι ≃o Set.range (t
oZ hι.some) where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`toZ` defines an `OrderIso` between `ι` and its range.
-/
noncomputable def orderIsoRangeToZOfLinearSuccPredArch [hι : Nonempty ι] :
    ι ≃o Set.range (toZ hι.some) where
  toEquiv := Equiv.ofInjective _ injective_toZ
  map_rel_iff' := by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) countable_of_linear_succ_pred_arch : Countable ι := by
  rcases isEmpty_or_nonempty ι with _ | hι
  · infer_instance
  · exact Countable.of_equiv _ orderIsoRangeToZOfLinearSuccPredArch.symm.toEquiv

set_option backward.isDefEq.respectTransparency.types false in
/-- If the order has neither bot nor top, `toZ` defines an `OrderIso` between `ι` and `ℤ`. -/
/-
**orderIsoIntOfLinearSuccPredArch** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：orderIsoIntOfLinearSuccPredArch [NoMaxOrder ι] [NoMinOrder ι] [hι : Nonemp
ty ι] : ι ≃o Int where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the order has neither bot nor top, `toZ` defines an `OrderIso` between `ι` an
d `ℤ`.
-/
noncomputable def orderIsoIntOfLinearSuccPredArch [NoMaxOrder ι] [NoMinOrder ι] [hι : Nonempty ι] :
    ι ≃o ℤ where
  toFun := toZ hι.some
  invFun n := if 0 ≤ n then succ^[n.toNat] hι.some else pred^[(-n).toNat] hι.some
  left_inv i := by
    rcases le_or_gt hι.some i with hi | hi
    · have h_nonneg : 0 ≤ toZ hι.some i := toZ_nonneg hi
      simp_rw [if_pos h_nonneg]
      exact iterate_succ_toZ i hi
    · have h_neg : toZ hι.some i < 0 := toZ_neg hi
      simp_rw [if_neg (not_le.mpr h_neg)]
      exact iterate_pred_toZ i hi
  right_inv n := by
    rcases le_or_gt 0 n with hn | hn
    · simp_rw [if_pos hn]
      rw [toZ_iterate_succ]
      exact Int.toNat_of_nonneg hn
    · simp_rw [if_neg (not_le.mpr hn)]
      rw [toZ_iterate_pred]
      simp only [hn.le, Int.toNat_of_nonneg, Int.neg_nonneg_of_nonpos, Int.neg_neg]
  map_rel_iff' := by simp

set_option backward.isDefEq.respectTransparency false in
/-- If the order has a bot but no top, `toZ` defines an `OrderIso` between `ι` and `ℕ`. -/
/-
**orderIsoNatOfLinearSuccPredArch** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：orderIsoNatOfLinearSuccPredArch [NoMaxOrder ι] [OrderBot ι] : ι ≃o Nat whe
re toFun i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the order has a bot but no top, `toZ` defines an `OrderIso` between `ι` and `
ℕ`.
-/
def orderIsoNatOfLinearSuccPredArch [NoMaxOrder ι] [OrderBot ι] : ι ≃o ℕ where
  toFun i := (toZ ⊥ i).toNat
  invFun n := succ^[n] ⊥
  left_inv i := by
    dsimp only
    exact iterate_succ_toZ i bot_le
  right_inv n := by
    dsimp only
    rw [toZ_iterate_succ]
    exact Int.toNat_natCast n
  map_rel_iff' := by
    intro i j
    simp only [Equiv.coe_fn_mk, Int.toNat_le]
    rw [← toZ_le_toZ (i0 := (⊥ : ι)), Int.toNat_of_nonneg (toZ_nonneg bot_le)]

set_option backward.isDefEq.respectTransparency false in
/-- If the order has both a bot and a top, `toZ` gives an `OrderIso` between `ι` and
`Finset.range n` for some `n`. -/
/-
**orderIsoRangeOfLinearSuccPredArch** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：orderIsoRangeOfLinearSuccPredArch [OrderBot ι] [OrderTop ι] : ι ≃o Finset.
range ((toZ ⊥ (⊤ : ι)).toNat + 1) where toFun i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the order has both a bot and a top, `toZ` gives an `OrderIso` between `ι` and
`Finset.range n` for some `n`.
-/
def orderIsoRangeOfLinearSuccPredArch [OrderBot ι] [OrderTop ι] :
    ι ≃o Finset.range ((toZ ⊥ (⊤ : ι)).toNat + 1) where
  toFun i :=
    ⟨(toZ ⊥ i).toNat,
      Finset.mem_range_succ_iff.mpr (Int.toNat_le_toNat (toZ_le_toZ.mpr le_top))⟩
  invFun n := succ^[n] ⊥
  left_inv i := iterate_succ_toZ i bot_le
  right_inv n := by
    ext1
    simp only
    refine le_antisymm ?_ ?_
    · rw [Int.toNat_le]
      exact toZ_iterate_succ_le _
    by_cases hn_max : IsMax (succ^[↑n] (⊥ : ι))
    · rw [← isTop_iff_isMax, isTop_iff_eq_top] at hn_max
      rw [hn_max]
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp n.prop)
    · rw [toZ_iterate_succ_of_not_isMax _ hn_max]
      simp only [Int.toNat_natCast, le_refl]
  map_rel_iff' := by
    intro i j
    simp only [Equiv.coe_fn_mk, Subtype.mk_le_mk, Int.toNat_le]
    rw [← toZ_le_toZ (i0 := (⊥ : ι)), Int.toNat_of_nonneg (toZ_nonneg bot_le)]

end OrderIso

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) Countable.of_linearOrder_locallyFiniteOrder [LocallyFiniteOrder ι] :
    Countable ι :=
  have := LinearLocallyFiniteOrder.succOrder ι
  have := LinearLocallyFiniteOrder.predOrder ι
  countable_of_linear_succ_pred_arch
