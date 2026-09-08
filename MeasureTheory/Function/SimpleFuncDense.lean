/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Density of simple functions

Show that each Borel measurable function can be approximated pointwise
by a sequence of simple functions.

## Main definitions

* `MeasureTheory.SimpleFunc.nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ ℕ`: the `SimpleFunc` sending
  each `x : α` to the point `e k` which is the nearest to `x` among `e 0`, ..., `e N`.
* `MeasureTheory.SimpleFunc.approxOn (f : β → α) (hf : Measurable f) (s : Set α) (y₀ : α)
  (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) : β →ₛ α` : a simple function that takes values in `s`
  and approximates `f`.

## Main results

* `tendsto_approxOn` (pointwise convergence): If `f x ∈ s`, then the sequence of simple
  approximations `MeasureTheory.SimpleFunc.approxOn f hf s y₀ h₀ n`, evaluated at `x`,
  tends to `f x` as `n` tends to `∞`.

## Notation

* `α →ₛ β` (local notation): the type of simple functions `α → β`.
-/

@[expose] public section

open Set Function Filter TopologicalSpace Metric MeasureTheory
open scoped Topology ENNReal

variable {α β : Type*}

noncomputable section

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

namespace SimpleFunc

/-! ### Pointwise approximation by simple functions -/


variable [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]

/-- `nearestPtInd e N x` is the index `k` such that `e k` is the nearest point to `x` among the
points `e 0`, ..., `e N`. If more than one point are at the same distance from `x`, then
`nearestPtInd e N x` returns the least of their indices. -/
/-
**MeasureTheory.SimpleFunc.nearestPtInd** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：{α : Type u_1} →   [inst : MeasurableSpace α] →     [inst_1 : PseudoEMetri
cSpace α] → [OpensMeasurableSpace α] → (ℕ → α) → ℕ → MeasureTheory.SimpleFunc α 
ℕ
参数：ℕ → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`nearestPtInd e N x` is the index `k` such that `e k` is the nearest point to `x
` among the
points `e 0`, ..., `e N`. If more than one point are at the same distance from `
x`, then
`nearestPtInd e N x` returns the least of their indices.
-/
noncomputable def nearestPtInd (e : ℕ → α) : ℕ → α →ₛ ℕ
  | 0 => const α 0
  | N + 1 =>
    piecewise (⋂ k ≤ N, { x | edist (e (N + 1)) x < edist (e k) x })
      (MeasurableSet.iInter fun _ =>
        MeasurableSet.iInter fun _ =>
          measurableSet_lt measurable_edist_right measurable_edist_right)
      (const α <| N + 1) (nearestPtInd e N)

/-- `nearestPt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`. If more than
one point are at the same distance from `x`, then `nearestPt e N x` returns the point with the
least possible index. -/
/-
**MeasureTheory.SimpleFunc.nearestPt** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Si
mpleFunc`。
形式化陈述：nearestPt (e : Nat -> α) (N : Nat) : α ->ₛ α
参数：e : Nat -> α；N : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`nearestPt e N x` is the nearest point to `x` among the points `e 0`, ..., `e N`
. If more than
one point are at the same distance from `x`, then `nearestPt e N x` returns the 
point with the
least possible index.
-/
noncomputable def nearestPt (e : ℕ → α) (N : ℕ) : α →ₛ α :=
  (nearestPtInd e N).map e

@[simp]
/-
**MeasureTheory.SimpleFunc.nearestPtInd_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.SimpleFunc`。
形式化陈述：nearestPtInd_zero (e : Nat -> α) : nearestPtInd e 0 = const α 0
参数：e : Nat -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nearestPtInd_zero (e : ℕ → α) : nearestPtInd e 0 = const α 0 :=
  rfl

@[simp]
/-
**MeasureTheory.SimpleFunc.nearestPt_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry.SimpleFunc`。
形式化陈述：nearestPt_zero (e : Nat -> α) : nearestPt e 0 = const α (e 0)
参数：e : Nat -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nearestPt_zero (e : ℕ → α) : nearestPt e 0 = const α (e 0) :=
  rfl
/-
**MeasureTheory.SimpleFunc.nearestPtInd_succ** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.SimpleFunc`。
形式化陈述：nearestPtInd_succ (e : Nat -> α) (N : Nat) (x : α) : nearestPtInd e (N + 1
) x = if forall k <= N, edist (e (N + 1)) x < edist (e k) x then N + 1 else near
estPtInd e N x
参数：e : Nat -> α；N : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nearestPtInd_succ (e : ℕ → α) (N : ℕ) (x : α) :
    nearestPtInd e (N + 1) x =
      if ∀ k ≤ N, edist (e (N + 1)) x < edist (e k) x then N + 1 else nearestPtInd e N x := by
  simp only [nearestPtInd, coe_piecewise, Set.piecewise]
  congr
  simp
/-
**MeasureTheory.SimpleFunc.nearestPtInd_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory.SimpleFunc`。
形式化陈述：nearestPtInd_le (e : Nat -> α) (N : Nat) (x : α) : nearestPtInd e N x <= N
参数：e : Nat -> α；N : Nat；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.SimpleFunc.nearestPtInd_succ`：nearestPtInd_succ (e : Nat -
> α) (N : Nat) (x : α) : nearestPtInd e (N + 1) x = if forall k <= N, edist (e (
N + 1)) x < edist (e k) x then N…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
-/
theorem nearestPtInd_le (e : ℕ → α) (N : ℕ) (x : α) : nearestPtInd e N x ≤ N := by
  induction N with
  | zero => simp
  | succ N ihN =>
    simp only [nearestPtInd_succ]
    split_ifs
    exacts [le_rfl, ihN.trans N.le_succ]
/-
**MeasureTheory.SimpleFunc.edist_nearestPt_le** 是 Mathlib 中的一个定理，位于命名空间 `Measure
Theory.SimpleFunc`。
形式化陈述：edist_nearestPt_le (e : Nat -> α) (x : α) {k N : Nat} (hk : k <= N) : edis
t (nearestPt e N x) x <= edist (e k) x
参数：e : Nat -> α；x : α；hk : k <= N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `MeasureTheory.SimpleFunc.nearestPtInd_succ`：nearestPtInd_succ (e : Nat -
> α) (N : Nat) (x : α) : nearestPtInd e (N + 1) x = if forall k <= N, edist (e (
N + 1)) x < edist (e k) x then N…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem edist_nearestPt_le (e : ℕ → α) (x : α) {k N : ℕ} (hk : k ≤ N) :
    edist (nearestPt e N x) x ≤ edist (e k) x := by
  induction N generalizing k with
  | zero => simp [nonpos_iff_eq_zero.1 hk]
  | succ N ihN =>
    simp only [nearestPt, nearestPtInd_succ, map_apply]
    split_ifs with h
    · rcases hk.eq_or_lt with (rfl | hk)
      exacts [le_rfl, (h k (Nat.lt_succ_iff.1 hk)).le]
    · push Not at h
      rcases h with ⟨l, hlN, hxl⟩
      rcases hk.eq_or_lt with (rfl | hk)
      exacts [(ihN hlN).trans hxl, ihN (Nat.lt_succ_iff.1 hk)]
/-
**MeasureTheory.SimpleFunc.tendsto_nearestPt** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.SimpleFunc`。
形式化陈述：tendsto_nearestPt {e : Nat -> α} {x : α} (hx : x in closure (range e)) : T
endsto (fun N => nearestPt e N x) atTop (𝓝 x)
参数：hx : x in closure (range e)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Metric.nhds_basis_eball`：nhds_basis_eball : (𝓝 x).HasBasis (fun ε : Real
>=0∞ => 0 < ε) (eball x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EMetric.mem_closure_iff`：mem_closure_iff : x in closure s ↔ forall ε > 0
, exists y in s, edist x y < ε
· 使用定理 `trivial`：True
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.SimpleFunc.edist_nearestPt_le`：edist_nearestPt_le (e : Nat
 -> α) (x : α) {k N : Nat} (hk : k <= N) : edist (nearestPt e N x) x <= edist (e
 k) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
-/
theorem tendsto_nearestPt {e : ℕ → α} {x : α} (hx : x ∈ closure (range e)) :
    Tendsto (fun N => nearestPt e N x) atTop (𝓝 x) := by
  refine (atTop_basis.tendsto_iff nhds_basis_eball).2 fun ε hε => ?_
  rcases EMetric.mem_closure_iff.1 hx ε hε with ⟨_, ⟨N, rfl⟩, hN⟩
  rw [edist_comm] at hN
  exact ⟨N, trivial, fun n hn => (edist_nearestPt_le e x hn).trans_lt hN⟩

variable [MeasurableSpace β] {f : β → α}

/-- Approximate a measurable function by a sequence of simple functions `F n` such that
`F n x ∈ s`. -/
/-
**MeasureTheory.SimpleFunc.approxOn** 是 Mathlib 中的一个定义，位于命名空间 `MeasureTheory.Sim
pleFunc`。
形式化陈述：approxOn (f : β -> α) (hf : Measurable f) (s : Set α) (y₀ : α) (h₀ : y₀ in
 s) [SeparableSpace s] (n : Nat) : β ->ₛ α
参数：f : β -> α；hf : Measurable f；s : Set α；y₀ : α；h₀ : y₀ in s；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Approximate a measurable function by a sequence of simple functions `F n` such t
hat
`F n x ∈ s`.
-/
noncomputable def approxOn (f : β → α) (hf : Measurable f) (s : Set α) (y₀ : α) (h₀ : y₀ ∈ s)
    [SeparableSpace s] (n : ℕ) : β →ₛ α :=
  haveI : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  comp (nearestPt (fun k => Nat.casesOn k y₀ ((↑) ∘ denseSeq s) : ℕ → α) n) f hf

@[simp]
/-
**MeasureTheory.SimpleFunc.approxOn_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：approxOn_zero {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : 
y₀ in s) [SeparableSpace s] (x : β) : approxOn f hf s y₀ h₀ 0 x = y₀
参数：hf : Measurable f；h₀ : y₀ in s；x : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem approxOn_zero {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) : approxOn f hf s y₀ h₀ 0 x = y₀ :=
  rfl
/-
**MeasureTheory.SimpleFunc.approxOn_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
.SimpleFunc`。
形式化陈述：approxOn_mem {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y
₀ in s) [SeparableSpace s] (n : Nat) (x : β) : approxOn f hf s y₀ h₀ n x in s
参数：hf : Measurable f；h₀ : y₀ in s；n : Nat；x : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
-/
theorem approxOn_mem {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (n : ℕ) (x : β) : approxOn f hf s y₀ h₀ n x ∈ s := by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  suffices ∀ n, (Nat.casesOn n y₀ ((↑) ∘ denseSeq s) : α) ∈ s by apply this
  rintro (_ | n)
  exacts [h₀, Subtype.mem _]
/-
**MeasureTheory.SimpleFunc.approxOn_range_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Meas
ureTheory.SimpleFunc`。
形式化陈述：approxOn_range_nonneg [Zero α] [Preorder α] {f : β -> α} (hf : 0 <= f) {hf
m : Measurable f} [SeparableSpace (range f union {0} : Set α)] (n : Nat) : 0 <= 
approxOn f hfm (range f union {0}) 0 (by simp) n
参数：hf : 0 <= f；range f union {0} : Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MeasureTheory.SimpleFunc.approxOn_mem`：approxOn_mem {f : β -> α} (hf : M
easurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [SeparableSpace s] (n : Nat) (x
 : β) : approxOn f hf s y₀ …
-/
lemma approxOn_range_nonneg [Zero α] [Preorder α] {f : β → α}
    (hf : 0 ≤ f) {hfm : Measurable f} [SeparableSpace (range f ∪ {0} : Set α)] (n : ℕ) :
    0 ≤ approxOn f hfm (range f ∪ {0}) 0 (by simp) n := by
  have : range f ∪ {0} ⊆ Set.Ici 0 := by
    simp only [Set.union_singleton, Set.insert_subset_iff, Set.mem_Ici, le_refl, true_and]
    rintro - ⟨x, rfl⟩
    exact hf x
  exact fun _ ↦ this <| approxOn_mem ..

@[simp]
/-
**MeasureTheory.SimpleFunc.approxOn_comp** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheor
y.SimpleFunc`。
形式化陈述：approxOn_comp {γ : Type*} [MeasurableSpace γ] {f : β -> α} (hf : Measurabl
e f) {g : γ -> β} (hg : Measurable g) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [Separ
ableSpace s] (n : Nat) : approxOn (f ∘ g) (hf.comp hg) s y₀ h₀ n = (approxOn f h
f s y₀ h₀ n).comp g hg
参数：hf : Measurable f；hg : Measurable g；h₀ : y₀ in s；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
-/
theorem approxOn_comp {γ : Type*} [MeasurableSpace γ] {f : β → α} (hf : Measurable f) {g : γ → β}
    (hg : Measurable g) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [SeparableSpace s] (n : ℕ) :
    approxOn (f ∘ g) (hf.comp hg) s y₀ h₀ n = (approxOn f hf s y₀ h₀ n).comp g hg :=
  rfl
/-
**MeasureTheory.SimpleFunc.tendsto_approxOn** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTh
eory.SimpleFunc`。
形式化陈述：tendsto_approxOn {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀
 : y₀ in s) [SeparableSpace s] {x : β} (hx : f x in closure s) : Tendsto (fun n 
=> approxOn f hf s y₀ h₀ n x) atTop (𝓝 <| f x)
参数：hf : Measurable f；h₀ : y₀ in s；hx : f x in closure s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.tendsto_nearestPt`：tendsto_nearestPt {e : Nat -
> α} {x : α} (hx : x in closure (range e)) : Tendsto (fun N => nearestPt e N x) 
atTop (𝓝 x)
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.range_casesOn`：range_casesOn {α : Type*} (x : α) (f : Nat -> α) : (S
et.range fun n => Nat.casesOn n x f : Set α) = {x} union Set.range f
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `closure_union`：closure_union : closure (s union t) = closure s union clo
sure t
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `TopologicalSpace.denseRange_denseSeq`：denseRange_denseSeq [SeparableSpac
e α] [Nonempty α] : DenseRange (denseSeq α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem tendsto_approxOn {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] {x : β} (hx : f x ∈ closure s) :
    Tendsto (fun n => approxOn f hf s y₀ h₀ n x) atTop (𝓝 <| f x) := by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  rw [← @Subtype.range_coe _ s, ← image_univ, ← (denseRange_denseSeq s).closure_eq] at hx
  simp -iota only [approxOn, coe_comp]
  refine tendsto_nearestPt (closure_minimal ?_ isClosed_closure hx)
  simp -iota only [Nat.range_casesOn, closure_union, range_comp]
  exact
    Subset.trans (image_closure_subset_closure_image continuous_subtype_val)
      subset_union_right
/-
**MeasureTheory.SimpleFunc.edist_approxOn_mono** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory.SimpleFunc`。
形式化陈述：edist_approxOn_mono {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} 
(h₀ : y₀ in s) [SeparableSpace s] (x : β) {m n : Nat} (h : m <= n) : edist (appr
oxOn f hf s y₀ h₀ n x) (f x) <= edist (approxOn f hf s y₀ h₀ m x) (f x)
参数：hf : Measurable f；h₀ : y₀ in s；x : β；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.edist_nearestPt_le`：edist_nearestPt_le (e : Nat
 -> α) (x : α) {k N : Nat} (hk : k <= N) : edist (nearestPt e N x) x <= edist (e
 k) x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.SimpleFunc.nearestPtInd_le`：nearestPtInd_le (e : Nat -> α)
 (N : Nat) (x : α) : nearestPtInd e N x <= N
-/
theorem edist_approxOn_mono {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) {m n : ℕ} (h : m ≤ n) :
    edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist (approxOn f hf s y₀ h₀ m x) (f x) := by
  dsimp only [approxOn, coe_comp, Function.comp_def]
  exact edist_nearestPt_le _ _ ((nearestPtInd_le _ _ _).trans h)
/-
**MeasureTheory.SimpleFunc.edist_approxOn_le** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory.SimpleFunc`。
形式化陈述：edist_approxOn_le {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h
₀ : y₀ in s) [SeparableSpace s] (x : β) (n : Nat) : edist (approxOn f hf s y₀ h₀
 n x) (f x) <= edist y₀ (f x)
参数：hf : Measurable f；h₀ : y₀ in s；x : β；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.SimpleFunc.edist_approxOn_mono`：edist_approxOn_mono {f : β
 -> α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [SeparableSpace s
] (x : β) {m n : Nat} (h : m <= n)…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
theorem edist_approxOn_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) (n : ℕ) : edist (approxOn f hf s y₀ h₀ n x) (f x) ≤ edist y₀ (f x) :=
  edist_approxOn_mono hf h₀ x zero_le
/-
**MeasureTheory.SimpleFunc.edist_approxOn_y0_le** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory.SimpleFunc`。
形式化陈述：edist_approxOn_y0_le {f : β -> α} (hf : Measurable f) {s : Set α} {y₀ : α}
 (h₀ : y₀ in s) [SeparableSpace s] (x : β) (n : Nat) : edist y₀ (approxOn f hf s
 y₀ h₀ n x) <= edist y₀ (f x) + edist y₀ (f x)
参数：hf : Measurable f；h₀ : y₀ in s；x : β；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_triangle_right`：edist_triangle_right (x y z : α) : edist x y <= ed
ist x z + edist y z
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.SimpleFunc.edist_approxOn_le`：edist_approxOn_le {f : β -> 
α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ in s) [SeparableSpace s] (x
 : β) (n : Nat) : edist (approxO…
-/
theorem edist_approxOn_y0_le {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s)
    [SeparableSpace s] (x : β) (n : ℕ) :
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤ edist y₀ (f x) + edist y₀ (f x) :=
  calc
    edist y₀ (approxOn f hf s y₀ h₀ n x) ≤
        edist y₀ (f x) + edist (approxOn f hf s y₀ h₀ n x) (f x) :=
      edist_triangle_right _ _ _
    _ ≤ edist y₀ (f x) + edist y₀ (f x) := by grw [edist_approxOn_le hf h₀ x n]

end SimpleFunc

end MeasureTheory

section CompactSupport

variable {X Y α : Type*} [Zero α]
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y]

/-- A continuous function with compact support on a product space can be uniformly approximated by
simple functions. The subtlety is that we do not assume that the spaces are separable, so the
product of the Borel sigma algebras might not contain all open sets, but still it contains enough
of them to approximate compactly supported continuous functions. -/
/-
**HasCompactSupport.exists_simpleFunc_approx_of_prod** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：HasCompactSupport.exists_simpleFunc_approx_of_prod [PseudoMetricSpace α] {
f : X × Y -> α} (hf : Continuous f) (h'f : HasCompactSupport f) {ε : Real} (hε :
 0 < ε) : exists (g : SimpleFunc (X × Y) α), forall x, dist (f x) (g x) < ε
参数：hf : Continuous f；h'f : HasCompactSupport f；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.induction_on`：IsCompact.induction_on (hs : IsCompact s) {p : S
et X -> Prop} (he : p ∅) (hmono : forall ⦃s t⦄, s subseteq t -> p t -> p s) (hun
ion : forall…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasurableSet.union`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∪ s₂)
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_union`：mem_union (x : α) (a b : Set α) : x in a union b ↔ x in a
 ∨ x in b
· 使用定理 `mem_nhds_prod_iff'`：mem_nhds_prod_iff' {x : X} {y : Y} {s : Set (X × Y)}
 : s in 𝓝 (x, y) ↔ exists u v, IsOpen u ∧ x in u ∧ IsOpen v ∧ y in v ∧ u ×ˢ v su
bseteq s
· 使用定理 `Metric.continuousAt_iff'`：continuousAt_iff' [TopologicalSpace β] {f : β 
-> α} {b : β} : ContinuousAt f b ↔ forall ε > 0, forallᶠ x in 𝓝 b, dist (f x) (f
 b) < ε
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `IsOpen.prod`：IsOpen.prod {s : Set X} {t : Set Y} (hs : IsOpen s) (ht : I
sOpen t) : IsOpen (s ×ˢ t)
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
A continuous function with compact support on a product space can be uniformly a
pproximated by
simple functions. The subtlety is that we do not assume that the spaces are sepa
rable, so the
product of the Borel sigma algebras might not contain all open sets, but still i
t contains enough
of them to approximate compactly supported continuous functions.
-/
lemma HasCompactSupport.exists_simpleFunc_approx_of_prod [PseudoMetricSpace α]
    {f : X × Y → α} (hf : Continuous f) (h'f : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : SimpleFunc (X × Y) α), ∀ x, dist (f x) (g x) < ε := by
  have M : ∀ (K : Set (X × Y)), IsCompact K →
      ∃ (g : SimpleFunc (X × Y) α), ∃ (s : Set (X × Y)), MeasurableSet s ∧ K ⊆ s ∧
      ∀ x ∈ s, dist (f x) (g x) < ε := by
    intro K hK
    apply IsCompact.induction_on
      (p := fun t ↦ ∃ (g : SimpleFunc (X × Y) α), ∃ (s : Set (X × Y)), MeasurableSet s ∧ t ⊆ s ∧
        ∀ x ∈ s, dist (f x) (g x) < ε) hK
    · exact ⟨0, ∅, by simp⟩
    · intro t t' htt' ⟨g, s, s_meas, ts, hg⟩
      exact ⟨g, s, s_meas, htt'.trans ts, hg⟩
    · intro t t' ⟨g, s, s_meas, ts, hg⟩ ⟨g', s', s'_meas, t's', hg'⟩
      refine ⟨g.piecewise s s_meas g', s ∪ s', s_meas.union s'_meas,
        union_subset_union ts t's', fun p hp ↦ ?_⟩
      by_cases H : p ∈ s
      · simpa [H, SimpleFunc.piecewise_apply] using hg p H
      · simp only [SimpleFunc.piecewise_apply, H, ite_false]
        apply hg'
        simpa [H] using (mem_union _ _ _).1 hp
    · rintro ⟨x, y⟩ -
      obtain ⟨u, v, hu, xu, hv, yv, huv⟩ : ∃ u v, IsOpen u ∧ x ∈ u ∧ IsOpen v ∧ y ∈ v ∧
        u ×ˢ v ⊆ {z | dist (f z) (f (x, y)) < ε} :=
          mem_nhds_prod_iff'.1 <| Metric.continuousAt_iff'.1 hf.continuousAt ε hε
      refine ⟨u ×ˢ v, nhdsWithin_le_nhds <| (hu.prod hv).mem_nhds (mk_mem_prod xu yv), ?_⟩
      exact ⟨SimpleFunc.const _ (f (x, y)), u ×ˢ v, hu.measurableSet.prod hv.measurableSet,
        Subset.rfl, fun z hz ↦ huv hz⟩
  obtain ⟨g, s, s_meas, fs, hg⟩ : ∃ (g : SimpleFunc (X × Y) α) (s : Set (X × Y)),
    MeasurableSet s ∧ tsupport f ⊆ s ∧ ∀ (x : X × Y), x ∈ s → dist (f x) (g x) < ε := M _ h'f
  refine ⟨g.piecewise s s_meas 0, fun p ↦ ?_⟩
  by_cases H : p ∈ s
  · simpa [H, SimpleFunc.piecewise_apply] using hg p H
  · have : f p = 0 := by
      contrapose! H
      rw [← Function.mem_support] at H
      exact fs (subset_tsupport _ H)
    simp [SimpleFunc.piecewise_apply, H, this, hε]

/-- A continuous function with compact support on a product space is measurable for the product
sigma-algebra. The subtlety is that we do not assume that the spaces are separable, so the
product of the Borel sigma algebras might not contain all open sets, but still it contains enough
of them to approximate compactly supported continuous functions. -/
/-
**HasCompactSupport.measurable_of_prod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：HasCompactSupport.measurable_of_prod [TopologicalSpace α] [PseudoMetrizabl
eSpace α] [MeasurableSpace α] [BorelSpace α] {f : X × Y -> α} (hf : Continuous f
) (h'f : HasCompactSupport f) : Measurable f
参数：hf : Continuous f；h'f : HasCompactSupport f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_strictAnti_tendsto`：exists_seq_strictAnti_tendsto [DenselyOrd
ered α] [NoMaxOrder α] [FirstCountableTopology α] (x : α) : exists u : Nat -> α,
 StrictAnti u ∧ (fo…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `HasCompactSupport.exists_simpleFunc_approx_of_prod`：HasCompactSupport.ex
ists_simpleFunc_approx_of_prod [PseudoMetricSpace α] {f : X × Y -> α} (hf : Cont
inuous f) (h'f : HasCompactSupport f) {ε…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_iff_dist_tendsto_zero`：tendsto_iff_dist_tendsto_zero {f : β -> α
} {x : Filter β} {a : α} : Tendsto f x (𝓝 a) ↔ Tendsto (fun b => dist (f b) a) x
 (𝓝 0)
· 使用引理 `squeeze_zero`：squeeze_zero {α} {f g : α -> Real} {t₀ : Filter α} (hf : f
orall t, 0 <= f t) (hft : forall t, f t <= g t) (g0 : Tendsto g t₀ (𝓝 0)) : Tend
st…
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `measurable_of_tendsto_metrizable`：measurable_of_tendsto_metrizable {f : 
Nat -> α -> β} {g : α -> β} (hf : forall i, Measurable (f i)) (lim : Tendsto f a
tTop (𝓝 g)) : Measurab…
· 使用定理 `MeasureTheory.SimpleFunc.measurable`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β]   (f : MeasureTheory.Simple
Func α β), Measurable ⇑f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A continuous function with compact support on a product space is measurable for 
the product
sigma-algebra. The subtlety is that we do not assume that the spaces are separab
le, so the
product of the Borel sigma algebras might not contain all open sets, but still i
t contains enough
of them to approximate compactly supported continuous functions.
-/
lemma HasCompactSupport.measurable_of_prod
    [TopologicalSpace α] [PseudoMetrizableSpace α] [MeasurableSpace α] [BorelSpace α]
    {f : X × Y → α} (hf : Continuous f) (h'f : HasCompactSupport f) :
    Measurable f := by
  let : PseudoMetricSpace α := TopologicalSpace.pseudoMetrizableSpacePseudoMetric α
  obtain ⟨u, -, u_pos, u_lim⟩ : ∃ u, StrictAnti u ∧ (∀ (n : ℕ), 0 < u n) ∧ Tendsto u atTop (𝓝 0) :=
    exists_seq_strictAnti_tendsto (0 : ℝ)
  have : ∀ n, ∃ (g : SimpleFunc (X × Y) α), ∀ x, dist (f x) (g x) < u n :=
    fun n ↦ h'f.exists_simpleFunc_approx_of_prod hf (u_pos n)
  choose g hg using this
  have A : ∀ x, Tendsto (fun n ↦ g n x) atTop (𝓝 (f x)) := by
    intro x
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) u_lim
    rw [dist_comm]
    exact (hg n x).le
  apply measurable_of_tendsto_metrizable (fun n ↦ (g n).measurable) (tendsto_pi_nhds.2 A)

end CompactSupport

