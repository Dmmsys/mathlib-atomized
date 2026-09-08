/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Analysis.Asymptotics.LinearGrowth
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-!
# Exponential growth

This file defines the exponential growth of a sequence `u : ℕ → ℝ≥0∞`. This notion comes in two
versions, using a `liminf` and a `limsup` respectively.

## Main definitions

- `expGrowthInf`, `expGrowthSup`: respectively, `liminf` and `limsup` of `log (u n) / n`.
- `expGrowthInfTopHom`, `expGrowthSupBotHom`: the functions `expGrowthInf`, `expGrowthSup`
  as homomorphisms preserving finitary `Inf`/`Sup` respectively.

## Tags

asymptotics, exponential
-/

@[expose] public section

namespace ExpGrowth

open ENNReal EReal Filter Function LinearGrowth
open scoped Topology

/-! ### Definition -/

/-- Lower exponential growth of a sequence of extended nonnegative real numbers. -/
/-
**ExpGrowth.expGrowthInf** 是 Mathlib 中的一个定义，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf (u : Nat -> Real>=0∞) : EReal
参数：u : Nat -> Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lower exponential growth of a sequence of extended nonnegative real numbers.
-/
noncomputable def expGrowthInf (u : ℕ → ℝ≥0∞) : EReal := liminf (fun n ↦ log (u n) / n) atTop

/-- Upper exponential growth of a sequence of extended nonnegative real numbers. -/
/-
**ExpGrowth.expGrowthSup** 是 Mathlib 中的一个定义，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup (u : Nat -> Real>=0∞) : EReal
参数：u : Nat -> Real>=0∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upper exponential growth of a sequence of extended nonnegative real numbers.
-/
noncomputable def expGrowthSup (u : ℕ → ℝ≥0∞) : EReal := limsup (fun n ↦ log (u n) / n) atTop
/-
**ExpGrowth.expGrowthInf_def** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_def {u : Nat -> Real>=0∞} : expGrowthInf u = linearGrowthInf 
(log ∘ u)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma expGrowthInf_def {u : ℕ → ℝ≥0∞} :
    expGrowthInf u = linearGrowthInf (log ∘ u) := by
  rfl
/-
**ExpGrowth.expGrowthSup_def** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_def {u : Nat -> Real>=0∞} : expGrowthSup u = linearGrowthSup 
(log ∘ u)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma expGrowthSup_def {u : ℕ → ℝ≥0∞} :
    expGrowthSup u = linearGrowthSup (log ∘ u) := by
  rfl

/-! ### Basic properties -/

section basic_properties

variable {u v : ℕ → ℝ≥0∞} {a : EReal} {b : ℝ≥0∞}

/-
**ExpGrowth.expGrowthInf_congr** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_congr (h : u =ᶠ[atTop] v) : expGrowthInf u = expGrowthInf v
参数：h : u =ᶠ[atTop] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_congr`：liminf_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : liminf u 
f = limin…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
lemma expGrowthInf_congr (h : u =ᶠ[atTop] v) :
    expGrowthInf u = expGrowthInf v :=
  liminf_congr (h.mono fun _ uv ↦ uv ▸ rfl)
/-
**ExpGrowth.expGrowthSup_congr** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_congr (h : u =ᶠ[atTop] v) : expGrowthSup u = expGrowthSup v
参数：h : u =ᶠ[atTop] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
lemma expGrowthSup_congr (h : u =ᶠ[atTop] v) :
    expGrowthSup u = expGrowthSup v :=
  limsup_congr (h.mono fun _ uv ↦ uv ▸ rfl)
/-
**ExpGrowth.expGrowthInf_eventually_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowt
h`。
形式化陈述：expGrowthInf_eventually_monotone (h : u <=ᶠ[atTop] v) : expGrowthInf u <= 
expGrowthInf v
参数：h : u <=ᶠ[atTop] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_le_liminf`：liminf_le_liminf {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a <= v a) (h
u : f.IsBound…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `EReal.monotone_div_right_of_nonneg`：monotone_div_right_of_nonneg (h : 0 
<= b) : Monotone fun a => a / b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `ENNReal.log_monotone`：log_monotone : Monotone log
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
-/
lemma expGrowthInf_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    expGrowthInf u ≤ expGrowthInf v :=
  liminf_le_liminf (h.mono fun n uv ↦ monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))
/-
**ExpGrowth.expGrowthInf_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_monotone : Monotone expGrowthInf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_eventually_monotone`：expGrowthInf_eventually_mono
tone (h : u <=ᶠ[atTop] v) : expGrowthInf u <= expGrowthInf v
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma expGrowthInf_monotone : Monotone expGrowthInf :=
  fun _ _ uv ↦ expGrowthInf_eventually_monotone (Eventually.of_forall uv)
/-
**ExpGrowth.expGrowthSup_eventually_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowt
h`。
形式化陈述：expGrowthSup_eventually_monotone (h : u <=ᶠ[atTop] v) : expGrowthSup u <= 
expGrowthSup v
参数：h : u <=ᶠ[atTop] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_le_limsup`：limsup_le_limsup {α : Type*} [ConditionallyComp
leteLattice β] {f : Filter α} {u v : α -> β} (h : u <=ᶠ[f] v) (hu : f.IsCobounde
dUnder (· <= …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `EReal.monotone_div_right_of_nonneg`：monotone_div_right_of_nonneg (h : 0 
<= b) : Monotone fun a => a / b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `ENNReal.log_monotone`：log_monotone : Monotone log
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
-/
lemma expGrowthSup_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    expGrowthSup u ≤ expGrowthSup v :=
  limsup_le_limsup (h.mono fun n uv ↦ monotone_div_right_of_nonneg n.cast_nonneg' (log_monotone uv))
/-
**ExpGrowth.expGrowthSup_monotone** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_monotone : Monotone expGrowthSup
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_eventually_monotone`：expGrowthSup_eventually_mono
tone (h : u <=ᶠ[atTop] v) : expGrowthSup u <= expGrowthSup v
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma expGrowthSup_monotone : Monotone expGrowthSup :=
  fun _ _ uv ↦ expGrowthSup_eventually_monotone (Eventually.of_forall uv)
/-
**ExpGrowth.expGrowthInf_le_expGrowthSup** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_le_expGrowthSup : expGrowthInf u <= expGrowthSup u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_le_limsup`：liminf_le_limsup {f : Filter β} [NeBot f] {u : 
β -> α} (h : f.IsBoundedUnder (· <= ·) u
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
-/
lemma expGrowthInf_le_expGrowthSup : expGrowthInf u ≤ expGrowthSup u := liminf_le_limsup
/-
**ExpGrowth.expGrowthInf_le_expGrowthSup_of_frequently_le** 是 Mathlib 中的一个引理，位于命
名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_le_expGrowthSup_of_frequently_le (h : existsᶠ n in atTop, u n
 <= v n) : expGrowthInf u <= expGrowthSup v
参数：h : existsᶠ n in atTop, u n <= v n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.liminf_le_limsup_of_frequently_le`：liminf_le_limsup_of_frequently
_le {v : α -> β} (h : existsᶠ x in f, u x <= v x) (h₁ : f.IsBoundedUnder (· >= ·
) u
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用引理 `EReal.div_le_div_right_of_nonneg`：div_le_div_right_of_nonneg (h : 0 <= c
) (h' : a <= b) : a / c <= b / c
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `ENNReal.log_le_log`：∀ {x y : ENNReal}, x ≤ y → x.log ≤ y.log
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
-/
lemma expGrowthInf_le_expGrowthSup_of_frequently_le (h : ∃ᶠ n in atTop, u n ≤ v n) :
    expGrowthInf u ≤ expGrowthSup v :=
  liminf_le_limsup_of_frequently_le <| h.mono fun n u_v ↦ by gcongr
/-
**ExpGrowth.expGrowthInf_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_le_iff : expGrowthInf u <= a ↔ forall b > a, existsᶠ n : Nat 
in atTop, u n <= exp (b * n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExpGrowth.expGrowthInf.eq_1`：∀ (u : ℕ → ENNReal), ExpGrowth.expGrowthInf
 u = Filter.liminf (fun n => (u n).log / ↑n) Filter.atTop
· 使用定理 `Filter.liminf_le_iff'`：liminf_le_iff' [DenselyOrdered β] {x : β} (h₁ : f
.IsCoboundedUnder (· >= ·) u
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用引理 `Filter.frequently_congr`：frequently_congr {p q : α -> Prop} {f : Filter 
α} (h : forallᶠ x in f, p x ↔ q x) : (existsᶠ x in f, p x) ↔ existsᶠ x in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `EReal.div_le_iff_le_mul`：div_le_iff_le_mul (h : 0 < b) (h' : b != ⊤) : a
 / b <= c ↔ a <= b * c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `EReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : EReal) != ⊤
· 使用定理 `EReal.log_exp`：∀ (x : EReal), x.exp.log = x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
-/
lemma expGrowthInf_le_iff :
    expGrowthInf u ≤ a ↔ ∀ b > a, ∃ᶠ n : ℕ in atTop, u n ≤ exp (b * n) := by
  rw [expGrowthInf, liminf_le_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), ← log_exp (n * b), mul_comm _ b]
  exact logOrderIso.le_iff_le
/-
**ExpGrowth.le_expGrowthInf_iff** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：le_expGrowthInf_iff : a <= expGrowthInf u ↔ forall b < a, forallᶠ n : Nat 
in atTop, exp (b * n) <= u n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExpGrowth.expGrowthInf.eq_1`：∀ (u : ℕ → ENNReal), ExpGrowth.expGrowthInf
 u = Filter.liminf (fun n => (u n).log / ↑n) Filter.atTop
· 使用定理 `Filter.le_liminf_iff'`：le_liminf_iff' [DenselyOrdered β] {x : β} (h₁ : f
.IsCoboundedUnder (· >= ·) u
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `EReal.le_div_iff_mul_le`：le_div_iff_mul_le (h : b > 0) (h' : b != ⊤) : a
 <= c / b ↔ a * b <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `EReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : EReal) != ⊤
· 使用定理 `EReal.log_exp`：∀ (x : EReal), x.exp.log = x
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
-/
lemma le_expGrowthInf_iff :
    a ≤ expGrowthInf u ↔ ∀ b < a, ∀ᶠ n : ℕ in atTop, exp (b * n) ≤ u n := by
  rw [expGrowthInf, le_liminf_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n), ← log_exp (b * n)]
  exact logOrderIso.le_iff_le
/-
**ExpGrowth.expGrowthSup_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_le_iff : expGrowthSup u <= a ↔ forall b > a, forallᶠ n : Nat 
in atTop, u n <= exp (b * n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExpGrowth.expGrowthSup.eq_1`：∀ (u : ℕ → ENNReal), ExpGrowth.expGrowthSup
 u = Filter.limsup (fun n => (u n).log / ↑n) Filter.atTop
· 使用引理 `Filter.limsup_le_iff'`：limsup_le_iff' [DenselyOrdered β] {x : β} (h₁ : I
sCoboundedUnder (· <= ·) f u
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `EReal.div_le_iff_le_mul`：div_le_iff_le_mul (h : 0 < b) (h' : b != ⊤) : a
 / b <= c ↔ a <= b * c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `EReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : EReal) != ⊤
· 使用定理 `EReal.log_exp`：∀ (x : EReal), x.exp.log = x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
-/
lemma expGrowthSup_le_iff :
    expGrowthSup u ≤ a ↔ ∀ b > a, ∀ᶠ n : ℕ in atTop, u n ≤ exp (b * n) := by
  rw [expGrowthSup, limsup_le_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), ← log_exp (n * b), mul_comm _ b]
  exact logOrderIso.le_iff_le
/-
**ExpGrowth.le_expGrowthSup_iff** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：le_expGrowthSup_iff : a <= expGrowthSup u ↔ forall b < a, existsᶠ n : Nat 
in atTop, exp (b * n) <= u n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExpGrowth.expGrowthSup.eq_1`：∀ (u : ℕ → ENNReal), ExpGrowth.expGrowthSup
 u = Filter.limsup (fun n => (u n).log / ↑n) Filter.atTop
· 使用引理 `Filter.le_limsup_iff'`：le_limsup_iff' [DenselyOrdered β] {x : β} (h₁ : f
.IsCoboundedUnder (· <= ·) u
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用引理 `Filter.frequently_congr`：frequently_congr {p q : α -> Prop} {f : Filter 
α} (h : forallᶠ x in f, p x ↔ q x) : (existsᶠ x in f, p x) ↔ existsᶠ x in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `EReal.le_div_iff_mul_le`：le_div_iff_mul_le (h : b > 0) (h' : b != ⊤) : a
 <= c / b ↔ a * b <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `EReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : EReal) != ⊤
· 使用定理 `EReal.log_exp`：∀ (x : EReal), x.exp.log = x
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
-/
lemma le_expGrowthSup_iff :
    a ≤ expGrowthSup u ↔ ∀ b < a, ∃ᶠ n : ℕ in atTop, exp (b * n) ≤ u n := by
  rw [expGrowthSup, le_limsup_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n), ← log_exp (b * n)]
  exact logOrderIso.le_iff_le

/- Forward direction of `expGrowthInf_le_iff`. -/
/-
**ExpGrowth.frequently_le_exp** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：frequently_le_exp (h : expGrowthInf u < a) : existsᶠ n : Nat in atTop, u n
 <= exp (a * n)
参数：h : expGrowthInf u < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ExpGrowth.expGrowthInf_le_iff`：expGrowthInf_le_iff : expGrowthInf u <= a
 ↔ forall b > a, existsᶠ n : Nat in atTop, u n <= exp (b * n)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Forward direction of `expGrowthInf_le_iff`.
-/
lemma frequently_le_exp (h : expGrowthInf u < a) :
    ∃ᶠ n : ℕ in atTop, u n ≤ exp (a * n) :=
  expGrowthInf_le_iff.1 (le_refl (expGrowthInf u)) a h

/- Forward direction of `le_expGrowthInf_iff`. -/
/-
**ExpGrowth.eventually_exp_le** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：eventually_exp_le (h : a < expGrowthInf u) : forallᶠ n : Nat in atTop, exp
 (a * n) <= u n
参数：h : a < expGrowthInf u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ExpGrowth.le_expGrowthInf_iff`：le_expGrowthInf_iff : a <= expGrowthInf u
 ↔ forall b < a, forallᶠ n : Nat in atTop, exp (b * n) <= u n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Forward direction of `le_expGrowthInf_iff`.
-/
lemma eventually_exp_le (h : a < expGrowthInf u) :
    ∀ᶠ n : ℕ in atTop, exp (a * n) ≤ u n :=
  le_expGrowthInf_iff.1 (le_refl (expGrowthInf u)) a h

/- Forward direction of `expGrowthSup_le_iff`. -/
/-
**ExpGrowth.eventually_le_exp** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：eventually_le_exp (h : expGrowthSup u < a) : forallᶠ n : Nat in atTop, u n
 <= exp (a * n)
参数：h : expGrowthSup u < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ExpGrowth.expGrowthSup_le_iff`：expGrowthSup_le_iff : expGrowthSup u <= a
 ↔ forall b > a, forallᶠ n : Nat in atTop, u n <= exp (b * n)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Forward direction of `expGrowthSup_le_iff`.
-/
lemma eventually_le_exp (h : expGrowthSup u < a) :
    ∀ᶠ n : ℕ in atTop, u n ≤ exp (a * n) :=
  expGrowthSup_le_iff.1 (le_refl (expGrowthSup u)) a h

/- Forward direction of `le_expGrowthSup_iff`. -/
/-
**ExpGrowth.frequently_exp_le** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：frequently_exp_le (h : a < expGrowthSup u) : existsᶠ n : Nat in atTop, exp
 (a * n) <= u n
参数：h : a < expGrowthSup u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `ExpGrowth.le_expGrowthSup_iff`：le_expGrowthSup_iff : a <= expGrowthSup u
 ↔ forall b < a, existsᶠ n : Nat in atTop, exp (b * n) <= u n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Forward direction of `le_expGrowthSup_iff`.
-/
lemma frequently_exp_le (h : a < expGrowthSup u) :
    ∃ᶠ n : ℕ in atTop, exp (a * n) ≤ u n :=
  le_expGrowthSup_iff.1 (le_refl (expGrowthSup u)) a h
/-
**ExpGrowth._root_.Frequently.expGrowthInf_le** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrow
th`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Frequently.expGrowthInf_le (h : ∃ᶠ n : ℕ in atTop, u n ≤ exp (a * n)) :
    expGrowthInf u ≤ a := by
  apply expGrowthInf_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans ?_
  gcongr
/-
**ExpGrowth._root_.Eventually.le_expGrowthInf** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrow
th`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Eventually.le_expGrowthInf (h : ∀ᶠ n : ℕ in atTop, exp (a * n) ≤ u n) :
    a ≤ expGrowthInf u :=
  le_expGrowthInf_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' <| by gcongr
/-
**ExpGrowth._root_.Eventually.expGrowthSup_le** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrow
th`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Eventually.expGrowthSup_le (h : ∀ᶠ n : ℕ in atTop, u n ≤ exp (a * n)) :
    expGrowthSup u ≤ a :=
  expGrowthSup_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans <| by gcongr
/-
**ExpGrowth._root_.Frequently.le_expGrowthSup** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrow
th`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Frequently.le_expGrowthSup (h : ∃ᶠ n : ℕ in atTop, exp (a * n) ≤ u n) :
    a ≤ expGrowthSup u :=
  le_expGrowthSup_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' <| by gcongr

/-! ### Special cases -/

/-
**ExpGrowth.expGrowthSup_zero** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_zero : expGrowthSup 0 = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearGrowth.linearGrowthSup_bot`：linearGrowthSup_bot : linearGrowthSup 
(⊥ : Nat -> EReal) = (⊥ : EReal)
· 使用引理 `ExpGrowth.expGrowthSup_def`：expGrowthSup_def {u : Nat -> Real>=0∞} : exp
GrowthSup u = linearGrowthSup (log ∘ u)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Pi.bot_apply`：bot_apply [forall i, Bot (α' i)] (i : ι) : (⊥ : forall i, 
α' i) i = ⊥
· 使用定理 `ENNReal.log_zero`：ENNReal.log 0 = ⊥

--- 原说明 ---
### Special cases
-/
lemma expGrowthSup_zero : expGrowthSup 0 = ⊥ := by
  rw [← linearGrowthSup_bot, expGrowthSup_def]
  congr 1
  ext _
  rw [comp_apply, Pi.zero_apply, Pi.bot_apply, log_zero]
/-
**ExpGrowth.expGrowthInf_zero** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_zero : expGrowthInf 0 = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ExpGrowth.expGrowthSup_zero`：expGrowthSup_zero : expGrowthSup 0 = ⊥
· 使用引理 `ExpGrowth.expGrowthInf_le_expGrowthSup`：expGrowthInf_le_expGrowthSup : e
xpGrowthInf u <= expGrowthSup u
-/
lemma expGrowthInf_zero : expGrowthInf 0 = ⊥ := by
  apply le_bot_iff.1
  rw [← expGrowthSup_zero]
  exact expGrowthInf_le_expGrowthSup
/-
**ExpGrowth.expGrowthInf_top** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_top : expGrowthInf ⊤ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearGrowth.linearGrowthInf_top`：linearGrowthInf_top : linearGrowthInf 
⊤ = (⊤ : EReal)
· 使用引理 `ExpGrowth.expGrowthInf_def`：expGrowthInf_def {u : Nat -> Real>=0∞} : exp
GrowthInf u = linearGrowthInf (log ∘ u)
-/
lemma expGrowthInf_top : expGrowthInf ⊤ = ⊤ := by
  rw [← linearGrowthInf_top, expGrowthInf_def]
  rfl
/-
**ExpGrowth.expGrowthSup_top** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_top : expGrowthSup ⊤ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ExpGrowth.expGrowthInf_top`：expGrowthInf_top : expGrowthInf ⊤ = ⊤
· 使用引理 `ExpGrowth.expGrowthInf_le_expGrowthSup`：expGrowthInf_le_expGrowthSup : e
xpGrowthInf u <= expGrowthSup u
-/
lemma expGrowthSup_top : expGrowthSup ⊤ = ⊤ := by
  apply top_le_iff.1
  rw [← expGrowthInf_top]
  exact expGrowthInf_le_expGrowthSup
/-
**ExpGrowth.expGrowthInf_const** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_const (h : b != 0) (h' : b != ∞) : expGrowthInf (fun _ => b) 
= 0
参数：h : b != 0；h' : b != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.liminf_eq`：Filter.Tendsto.liminf_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : liminf u f = a
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `EReal.tendsto_const_div_atTop_nhds_zero_nat`：EReal.tendsto_const_div_atT
op_nhds_zero_nat {C : EReal} (h : C != ⊥) (h' : C != ⊤) : Tendsto (fun n : Nat =
> C / n) atTop (𝓝 0)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.log_eq_bot_iff`：∀ {x : ENNReal}, x.log = ⊥ ↔ x = 0
· 使用定理 `ENNReal.log_eq_top_iff`：∀ {x : ENNReal}, x.log = ⊤ ↔ x = ⊤
-/
lemma expGrowthInf_const (h : b ≠ 0) (h' : b ≠ ∞) : expGrowthInf (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat (fun k ↦ h (log_eq_bot_iff.1 k))
    (fun k ↦ h' (log_eq_top_iff.1 k))).liminf_eq
/-
**ExpGrowth.expGrowthSup_const** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_const (h : b != 0) (h' : b != ∞) : expGrowthSup (fun _ => b) 
= 0
参数：h : b != 0；h' : b != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.limsup_eq`：Filter.Tendsto.limsup_eq {f : Filter β} {u : β
 -> α} {a : α} [NeBot f] (h : Tendsto u f (𝓝 a)) : limsup u f = a
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `EReal.tendsto_const_div_atTop_nhds_zero_nat`：EReal.tendsto_const_div_atT
op_nhds_zero_nat {C : EReal} (h : C != ⊥) (h' : C != ⊤) : Tendsto (fun n : Nat =
> C / n) atTop (𝓝 0)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ENNReal.log_eq_bot_iff`：∀ {x : ENNReal}, x.log = ⊥ ↔ x = 0
· 使用定理 `ENNReal.log_eq_top_iff`：∀ {x : ENNReal}, x.log = ⊤ ↔ x = ⊤
-/
lemma expGrowthSup_const (h : b ≠ 0) (h' : b ≠ ∞) : expGrowthSup (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat (fun k ↦ h (log_eq_bot_iff.1 k))
    (fun k ↦ h' (log_eq_top_iff.1 k))).limsup_eq
/-
**ExpGrowth.expGrowthInf_pow** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_pow : expGrowthInf (fun n => b ^ n) = log b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExpGrowth.expGrowthInf.eq_1`：∀ (u : ℕ → ENNReal), ExpGrowth.expGrowthInf
 u = Filter.liminf (fun n => (u n).log / ↑n) Filter.atTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.liminf_const`：liminf_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : liminf (fun _ => b) f = b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.liminf_congr`：liminf_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : liminf u 
f = limin…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用引理 `EReal.div_eq_iff`：div_eq_iff (hbot : b != ⊥) (htop : b != ⊤) (hzero : b 
!= 0) : c / b = a ↔ c = a * b
· 使用定理 `EReal.natCast_ne_bot`：natCast_ne_bot (n : Nat) : (n : EReal) != ⊥
· 使用定理 `EReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : EReal) != ⊤
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `Nat.one_le_cast`：one_le_cast : 1 <= (n : α) ↔ 1 <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `ENNReal.log_pow`：log_pow {x : Real>=0∞} {n : Nat} : log (x ^ n) = n * lo
g x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma expGrowthInf_pow : expGrowthInf (fun n ↦ b ^ n) = log b := by
  rw [expGrowthInf, ← liminf_const (f := atTop (α := ℕ)) (log b)]
  refine liminf_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm, log_pow, mul_comm]
/-
**ExpGrowth.expGrowthSup_pow** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_pow : expGrowthSup (fun n => b ^ n) = log b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExpGrowth.expGrowthSup.eq_1`：∀ (u : ℕ → ENNReal), ExpGrowth.expGrowthSup
 u = Filter.limsup (fun n => (u n).log / ↑n) Filter.atTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.limsup_const`：limsup_const {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} [NeBot f] (b : β) : limsup (fun _ => b) f = b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用引理 `EReal.div_eq_iff`：div_eq_iff (hbot : b != ⊥) (htop : b != ⊤) (hzero : b 
!= 0) : c / b = a ↔ c = a * b
· 使用定理 `EReal.natCast_ne_bot`：natCast_ne_bot (n : Nat) : (n : EReal) != ⊥
· 使用定理 `EReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : EReal) != ⊤
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `Nat.one_le_cast`：one_le_cast : 1 <= (n : α) ↔ 1 <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `ENNReal.log_pow`：log_pow {x : Real>=0∞} {n : Nat} : log (x ^ n) = n * lo
g x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
lemma expGrowthSup_pow : expGrowthSup (fun n ↦ b ^ n) = log b := by
  rw [expGrowthSup, ← limsup_const (f := atTop (α := ℕ)) (log b)]
  refine limsup_congr (eventually_atTop.2 ⟨1, fun n n_1 ↦ ?_⟩)
  rw [EReal.div_eq_iff (natCast_ne_bot n) (natCast_ne_top n)
    (zero_lt_one.trans_le (Nat.one_le_cast.2 n_1)).ne.symm, log_pow, mul_comm]
/-
**ExpGrowth.expGrowthInf_exp** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_exp : expGrowthInf (fun n => exp (a * n)) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Frequently.expGrowthInf_le`：∀ {u : ℕ → ENNReal} {a : EReal}, (∃ᶠ (n : ℕ)
 in Filter.atTop, u n ≤ (a * ↑n).exp) → ExpGrowth.expGrowthInf u ≤ a
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eventually.le_expGrowthInf`：∀ {u : ℕ → ENNReal} {a : EReal}, (∀ᶠ (n : ℕ)
 in Filter.atTop, (a * ↑n).exp ≤ u n) → a ≤ ExpGrowth.expGrowthInf u
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma expGrowthInf_exp : expGrowthInf (fun n ↦ exp (a * n)) = a :=
  le_antisymm (Frequently.expGrowthInf_le (Frequently.of_forall fun _ ↦ le_refl _))
    (Eventually.le_expGrowthInf (Eventually.of_forall fun _ ↦ le_refl _))
/-
**ExpGrowth.expGrowthSup_exp** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_exp : expGrowthSup (fun n => exp (a * n)) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eventually.expGrowthSup_le`：∀ {u : ℕ → ENNReal} {a : EReal}, (∀ᶠ (n : ℕ)
 in Filter.atTop, u n ≤ (a * ↑n).exp) → ExpGrowth.expGrowthSup u ≤ a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Frequently.le_expGrowthSup`：∀ {u : ℕ → ENNReal} {a : EReal}, (∃ᶠ (n : ℕ)
 in Filter.atTop, (a * ↑n).exp ≤ u n) → a ≤ ExpGrowth.expGrowthSup u
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma expGrowthSup_exp : expGrowthSup (fun n ↦ exp (a * n)) = a :=
  le_antisymm (Eventually.expGrowthSup_le (Eventually.of_forall fun _ ↦ le_refl _))
    (Frequently.le_expGrowthSup (Frequently.of_forall fun _ ↦ le_refl _))

/-! ### Multiplication and inversion -/

/-
**ExpGrowth.le_expGrowthInf_mul** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：le_expGrowthInf_mul : expGrowthInf u + expGrowthInf v <= expGrowthInf (u *
 v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `EReal.le_liminf_add`：le_liminf_add : (liminf u f) + (liminf v f) <= limi
nf (u + v) f
· 使用定理 `Filter.liminf_congr`：liminf_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : liminf u 
f = limin…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.add_div_of_nonneg_right`：add_div_of_nonneg_right (h : 0 <= c) : (a
 + b) / c = a / c + b / c
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `ENNReal.log_mul_add`：log_mul_add {x y : Real>=0∞} : log (x * y) = log x 
+ log y

--- 原说明 ---
### Multiplication and inversion
-/
lemma le_expGrowthInf_mul :
    expGrowthInf u + expGrowthInf v ≤ expGrowthInf (u * v) := by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, ← add_div_of_nonneg_right n.cast_nonneg', log_mul_add]

/-- See `expGrowthInf_mul_le'` for a version with swapped argument `u` and `v`. -/
/-
**ExpGrowth.expGrowthInf_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_mul_le (h : expGrowthSup u != ⊥ ∨ expGrowthInf v != ⊤) (h' : 
expGrowthSup u != ⊤ ∨ expGrowthInf v != ⊥) : expGrowthInf (u * v) <= expGrowthSu
p u + expGrowthInf v
参数：h : expGrowthSup u != ⊥ ∨ expGrowthInf v != ⊤；h' : expGrowthSup u != ⊤ ∨ expG
rowthInf v != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LE α], b ≤ a → b =
 c → c ≤ a
· 使用引理 `EReal.liminf_add_le`：liminf_add_le (h : limsup u f != ⊥ ∨ liminf v f != 
⊤) (h' : limsup u f != ⊤ ∨ liminf v f != ⊥) : liminf (u + v) f <= (limsup u f) +
 (liminf …
· 使用定理 `Filter.liminf_congr`：liminf_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : liminf u 
f = limin…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.add_div_of_nonneg_right`：add_div_of_nonneg_right (h : 0 <= c) : (a
 + b) / c = a / c + b / c
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `ENNReal.log_mul_add`：log_mul_add {x y : Real>=0∞} : log (x * y) = log x 
+ log y

--- 原说明 ---
See `expGrowthInf_mul_le'` for a version with swapped argument `u` and `v`.
-/
lemma expGrowthInf_mul_le (h : expGrowthSup u ≠ ⊥ ∨ expGrowthInf v ≠ ⊤)
    (h' : expGrowthSup u ≠ ⊤ ∨ expGrowthInf v ≠ ⊥) :
    expGrowthInf (u * v) ≤ expGrowthSup u + expGrowthInf v := by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, ← add_div_of_nonneg_right n.cast_nonneg', log_mul_add]

/-- See `expGrowthInf_mul_le` for a version with swapped argument `u` and `v`. -/
/-
**ExpGrowth.expGrowthInf_mul_le'** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_mul_le' (h : expGrowthInf u != ⊥ ∨ expGrowthSup v != ⊤) (h' :
 expGrowthInf u != ⊤ ∨ expGrowthSup v != ⊥) : expGrowthInf (u * v) <= expGrowthI
nf u + expGrowthSup v
参数：h : expGrowthInf u != ⊥ ∨ expGrowthSup v != ⊤；h' : expGrowthInf u != ⊤ ∨ expG
rowthSup v != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ExpGrowth.expGrowthInf_mul_le`：expGrowthInf_mul_le (h : expGrowthSup u !
= ⊥ ∨ expGrowthInf v != ⊤) (h' : expGrowthSup u != ⊤ ∨ expGrowthInf v != ⊥) : ex
pGrowthInf (u * v) …
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a

--- 原说明 ---
See `expGrowthInf_mul_le` for a version with swapped argument `u` and `v`.
-/
lemma expGrowthInf_mul_le' (h : expGrowthInf u ≠ ⊥ ∨ expGrowthSup v ≠ ⊤)
    (h' : expGrowthInf u ≠ ⊤ ∨ expGrowthSup v ≠ ⊥) :
    expGrowthInf (u * v) ≤ expGrowthInf u + expGrowthSup v := by
  rw [mul_comm, add_comm]
  exact expGrowthInf_mul_le h'.symm h.symm

/-- See `le_expGrowthSup_mul'` for a version with swapped argument `u` and `v`. -/
/-
**ExpGrowth.le_expGrowthSup_mul** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：le_expGrowthSup_mul : expGrowthSup u + expGrowthInf v <= expGrowthSup (u *
 v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `EReal.le_limsup_add`：le_limsup_add : (limsup u f) + (liminf v f) <= lims
up (u + v) f
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `ENNReal.log_mul_add`：log_mul_add {x y : Real>=0∞} : log (x * y) = log x 
+ log y
· 使用引理 `EReal.add_div_of_nonneg_right`：add_div_of_nonneg_right (h : 0 <= c) : (a
 + b) / c = a / c + b / c
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal

--- 原说明 ---
See `le_expGrowthSup_mul'` for a version with swapped argument `u` and `v`.
-/
lemma le_expGrowthSup_mul : expGrowthSup u + expGrowthInf v ≤ expGrowthSup (u * v) := by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, log_mul_add, add_div_of_nonneg_right n.cast_nonneg']

/-- See `le_expGrowthSup_mul` for a version with swapped argument `u` and `v`. -/
/-
**ExpGrowth.le_expGrowthSup_mul'** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：le_expGrowthSup_mul' : expGrowthInf u + expGrowthSup v <= expGrowthSup (u 
* v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `ExpGrowth.le_expGrowthSup_mul`：le_expGrowthSup_mul : expGrowthSup u + ex
pGrowthInf v <= expGrowthSup (u * v)

--- 原说明 ---
See `le_expGrowthSup_mul` for a version with swapped argument `u` and `v`.
-/
lemma le_expGrowthSup_mul' : expGrowthInf u + expGrowthSup v ≤ expGrowthSup (u * v) := by
  rw [mul_comm, add_comm]
  exact le_expGrowthSup_mul
/-
**ExpGrowth.expGrowthSup_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_mul_le (h : expGrowthSup u != ⊥ ∨ expGrowthSup v != ⊤) (h' : 
expGrowthSup u != ⊤ ∨ expGrowthSup v != ⊥) : expGrowthSup (u * v) <= expGrowthSu
p u + expGrowthSup v
参数：h : expGrowthSup u != ⊥ ∨ expGrowthSup v != ⊤；h' : expGrowthSup u != ⊤ ∨ expG
rowthSup v != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LE α], b ≤ a → b =
 c → c ≤ a
· 使用引理 `EReal.limsup_add_le`：limsup_add_le (h : limsup u f != ⊥ ∨ limsup v f != 
⊤) (h' : limsup u f != ⊤ ∨ limsup v f != ⊥) : limsup (u + v) f <= (limsup u f) +
 (limsup …
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用引理 `Pi.mul_apply`：mul_apply (f g : forall i, M i) (i : ι) : (f * g) i = f i 
* g i
· 使用定理 `ENNReal.log_mul_add`：log_mul_add {x y : Real>=0∞} : log (x * y) = log x 
+ log y
· 使用引理 `EReal.add_div_of_nonneg_right`：add_div_of_nonneg_right (h : 0 <= c) : (a
 + b) / c = a / c + b / c
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
-/
lemma expGrowthSup_mul_le (h : expGrowthSup u ≠ ⊥ ∨ expGrowthSup v ≠ ⊤)
    (h' : expGrowthSup u ≠ ⊤ ∨ expGrowthSup v ≠ ⊥) :
    expGrowthSup (u * v) ≤ expGrowthSup u + expGrowthSup v := by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.mul_apply, log_mul_add, add_div_of_nonneg_right n.cast_nonneg']
/-
**ExpGrowth.expGrowthInf_inv** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_inv : expGrowthInf u⁻¹ = - expGrowthSup u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExpGrowth.expGrowthSup.eq_1`：∀ (u : ℕ → ENNReal), ExpGrowth.expGrowthSup
 u = Filter.limsup (fun n => (u n).log / ↑n) Filter.atTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.liminf_neg`：liminf_neg : liminf (-v) f = -limsup v f
· 使用定理 `Filter.liminf_congr`：liminf_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : liminf u 
f = limin…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用引理 `Pi.inv_apply`：inv_apply (f : forall i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `EReal.neg_mul`：∀ (x y : EReal), -x * y = -(x * y)
· 使用引理 `ENNReal.log_inv`：log_inv {x : Real>=0∞} : log x⁻¹ = - log x
-/
lemma expGrowthInf_inv : expGrowthInf u⁻¹ = - expGrowthSup u := by
  rw [expGrowthSup, ← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.inv_apply, div_eq_mul_inv, div_eq_mul_inv, ← EReal.neg_mul, log_inv]
/-
**ExpGrowth.expGrowthSup_inv** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_inv : expGrowthSup u⁻¹ = - expGrowthInf u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExpGrowth.expGrowthInf.eq_1`：∀ (u : ℕ → ENNReal), ExpGrowth.expGrowthInf
 u = Filter.liminf (fun n => (u n).log / ↑n) Filter.atTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.limsup_neg`：limsup_neg : limsup (-v) f = -liminf v f
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用引理 `Pi.inv_apply`：inv_apply (f : forall i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `EReal.neg_mul`：∀ (x y : EReal), -x * y = -(x * y)
· 使用引理 `ENNReal.log_inv`：log_inv {x : Real>=0∞} : log x⁻¹ = - log x
-/
lemma expGrowthSup_inv : expGrowthSup u⁻¹ = - expGrowthInf u := by
  rw [expGrowthInf, ← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.inv_apply, div_eq_mul_inv, div_eq_mul_inv, ← EReal.neg_mul, log_inv]

/-! ### Comparison -/

-- Bound on `expGrowthInf` under a `IsBigO` hypothesis. However, `ℝ≥0∞` is not normed, so the
-- `IsBigO` property is spelt out.
/-
**ExpGrowth.expGrowthInf_le_of_eventually_le** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowt
h`。
形式化陈述：expGrowthInf_le_of_eventually_le (hb : b != ∞) (h : forallᶠ n in atTop, u 
n <= b * v n) : expGrowthInf u <= expGrowthInf v
参数：hb : b != ∞；h : forallᶠ n in atTop, u n <= b * v n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ExpGrowth.expGrowthInf_eventually_monotone`：expGrowthInf_eventually_mono
tone (h : u <=ᶠ[atTop] v) : expGrowthInf u <= expGrowthInf v
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `ExpGrowth.expGrowthInf_zero`：expGrowthInf_zero : expGrowthInf 0 = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `ExpGrowth.expGrowthInf_mul_le`：expGrowthInf_mul_le (h : expGrowthSup u !
= ⊥ ∨ expGrowthInf v != ⊤) (h' : expGrowthSup u != ⊤ ∨ expGrowthInf v != ⊥) : ex
pGrowthInf (u * v) …
· 使用引理 `ExpGrowth.expGrowthSup_const`：expGrowthSup_const (h : b != 0) (h' : b !=
 ∞) : expGrowthSup (fun _ => b) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `EReal.zero_ne_bot`：zero_ne_bot : (0 : EReal) != ⊥
· 使用定理 `EReal.zero_ne_top`：zero_ne_top : (0 : EReal) != ⊤
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma expGrowthInf_le_of_eventually_le (hb : b ≠ ∞) (h : ∀ᶠ n in atTop, u n ≤ b * v n) :
    expGrowthInf u ≤ expGrowthInf v := by
  apply (expGrowthInf_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthInf_zero, bot_le]
  · apply (expGrowthInf_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthInf v)
    · exact .inl zero_ne_bot
    · exact .inl zero_ne_top

-- Bound on `expGrowthSup` under a `IsBigO` hypothesis. However, `ℝ≥0∞` is not normed, so the
-- `IsBigO` property is spelt out.
/-
**ExpGrowth.expGrowthSup_le_of_eventually_le** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowt
h`。
形式化陈述：expGrowthSup_le_of_eventually_le (hb : b != ∞) (h : forallᶠ n in atTop, u 
n <= b * v n) : expGrowthSup u <= expGrowthSup v
参数：hb : b != ∞；h : forallᶠ n in atTop, u n <= b * v n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ExpGrowth.expGrowthSup_eventually_monotone`：expGrowthSup_eventually_mono
tone (h : u <=ᶠ[atTop] v) : expGrowthSup u <= expGrowthSup v
· 使用定理 `eq_zero_or_pos`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Zero 
α] [IsBotZeroClass α] (a : α), a = 0 ∨ 0 < a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `ExpGrowth.expGrowthSup_zero`：expGrowthSup_zero : expGrowthSup 0 = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `ExpGrowth.expGrowthSup_mul_le`：expGrowthSup_mul_le (h : expGrowthSup u !
= ⊥ ∨ expGrowthSup v != ⊤) (h' : expGrowthSup u != ⊤ ∨ expGrowthSup v != ⊥) : ex
pGrowthSup (u * v) …
· 使用引理 `ExpGrowth.expGrowthSup_const`：expGrowthSup_const (h : b != 0) (h' : b !=
 ∞) : expGrowthSup (fun _ => b) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `EReal.zero_ne_bot`：zero_ne_bot : (0 : EReal) != ⊥
· 使用定理 `EReal.zero_ne_top`：zero_ne_top : (0 : EReal) != ⊤
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma expGrowthSup_le_of_eventually_le (hb : b ≠ ∞) (h : ∀ᶠ n in atTop, u n ≤ b * v n) :
    expGrowthSup u ≤ expGrowthSup v := by
  apply (expGrowthSup_eventually_monotone h).trans
  rcases eq_zero_or_pos b with rfl | b_pos
  · simp only [zero_mul, ← Pi.zero_def, expGrowthSup_zero, bot_le]
  · apply (expGrowthSup_mul_le _ _).trans_eq <;> rw [expGrowthSup_const b_pos.ne' hb]
    · exact zero_add (expGrowthSup v)
    · exact .inl zero_ne_bot
    · exact .inl zero_ne_top
/-
**ExpGrowth.expGrowthInf_of_eventually_ge** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_of_eventually_ge (hb : b != 0) (h : forallᶠ n in atTop, b * u
 n <= v n) : expGrowthInf u <= expGrowthInf v
参数：hb : b != 0；h : forallᶠ n in atTop, b * u n <= v n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用引理 `ExpGrowth.expGrowthInf_eventually_monotone`：expGrowthInf_eventually_mono
tone (h : u <=ᶠ[atTop] v) : expGrowthInf u <= expGrowthInf v
· 使用引理 `ExpGrowth.le_expGrowthInf_mul`：le_expGrowthInf_mul : expGrowthInf u + ex
pGrowthInf v <= expGrowthInf (u * v)
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.top_def`：∀ {ι : Type u_1} {α' : ι → Type u_2} [inst : (i : ι) → Top (
α' i)], ⊤ = fun x => ⊤
· 使用引理 `ExpGrowth.expGrowthInf_top`：expGrowthInf_top : expGrowthInf ⊤ = ⊤
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `ExpGrowth.expGrowthInf_const`：expGrowthInf_const (h : b != 0) (h' : b !=
 ∞) : expGrowthInf (fun _ => b) = 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma expGrowthInf_of_eventually_ge (hb : b ≠ 0) (h : ∀ᶠ n in atTop, b * u n ≤ v n) :
    expGrowthInf u ≤ expGrowthInf v := by
  apply (expGrowthInf_eventually_monotone h).trans' (le_expGrowthInf_mul.trans' _)
  rcases eq_top_or_lt_top b with rfl | b_top
  · rw [← Pi.top_def, expGrowthInf_top]
    exact le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hb b_top.ne, zero_add]
/-
**ExpGrowth.expGrowthSup_of_eventually_ge** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_of_eventually_ge (hb : b != 0) (h : forallᶠ n in atTop, b * u
 n <= v n) : expGrowthSup u <= expGrowthSup v
参数：hb : b != 0；h : forallᶠ n in atTop, b * u n <= v n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用引理 `ExpGrowth.expGrowthSup_eventually_monotone`：expGrowthSup_eventually_mono
tone (h : u <=ᶠ[atTop] v) : expGrowthSup u <= expGrowthSup v
· 使用引理 `ExpGrowth.le_expGrowthSup_mul'`：le_expGrowthSup_mul' : expGrowthInf u + 
expGrowthSup v <= expGrowthSup (u * v)
· 使用定理 `eq_top_or_lt_top`：eq_top_or_lt_top (a : α) : a = ⊤ ∨ a < ⊤
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ExpGrowth.expGrowthInf_top`：expGrowthInf_top : expGrowthInf ⊤ = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ExpGrowth.expGrowthInf_const`：expGrowthInf_const (h : b != 0) (h' : b !=
 ∞) : expGrowthInf (fun _ => b) = 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma expGrowthSup_of_eventually_ge (hb : b ≠ 0) (h : ∀ᶠ n in atTop, b * u n ≤ v n) :
    expGrowthSup u ≤ expGrowthSup v := by
  apply (expGrowthSup_eventually_monotone h).trans' (le_expGrowthSup_mul'.trans' _)
  rcases eq_top_or_lt_top b with rfl | b_top
  · exact expGrowthInf_top ▸ le_add_of_nonneg_left le_top
  · rw [expGrowthInf_const hb b_top.ne, zero_add]

/-! ### Infimum and supremum -/

/-
**ExpGrowth.expGrowthInf_inf** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_inf : expGrowthInf (u ⊓ v) = expGrowthInf u ⊓ expGrowthInf v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExpGrowth.expGrowthInf.eq_1`：∀ (u : ℕ → ENNReal), ExpGrowth.expGrowthInf
 u = Filter.liminf (fun n => (u n).log / ↑n) Filter.atTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `liminf_min`：liminf_min [ConditionallyCompleteLinearOrder β] {f : Filter 
α} {u v : α -> β} (h₁ : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.liminf_congr`：liminf_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : liminf u 
f = limin…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Pi.inf_apply`：∀ {ι : Type u_1} {α' : ι → Type u_2} [inst : (i : ι) → Min
 (α' i)] (f g : (i : ι) → α' i) (i : ι), (f ⊓ g) i = f i ⊓ g i
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
· 使用定理 `ENNReal.log_monotone`：log_monotone : Monotone log
· 使用引理 `EReal.monotone_div_right_of_nonneg`：monotone_div_right_of_nonneg (h : 0 
<= b) : Monotone fun a => a / b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal

--- 原说明 ---
### Infimum and supremum
-/
lemma expGrowthInf_inf : expGrowthInf (u ⊓ v) = expGrowthInf u ⊓ expGrowthInf v := by
  rw [expGrowthInf, expGrowthInf, expGrowthInf, ← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.inf_apply, log_monotone.map_min]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

/-- Lower exponential growth as an `InfTopHom`. -/
/-
**ExpGrowth.expGrowthInfTopHom** 是 Mathlib 中的一个定义，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInfTopHom : InfTopHom (Nat -> Real>=0∞) EReal where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthInf_inf`：expGrowthInf_inf : expGrowthInf (u ⊓ v) = ex
pGrowthInf u ⊓ expGrowthInf v
· 使用引理 `ExpGrowth.expGrowthInf_top`：expGrowthInf_top : expGrowthInf ⊤ = ⊤

--- 原说明 ---
Lower exponential growth as an `InfTopHom`.
-/
noncomputable def expGrowthInfTopHom : InfTopHom (ℕ → ℝ≥0∞) EReal where
  toFun := expGrowthInf
  map_inf' _ _ := expGrowthInf_inf
  map_top' := expGrowthInf_top
/-
**ExpGrowth.expGrowthInf_biInf** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_biInf {α : Type*} (u : α -> Nat -> Real>=0∞) {s : Set α} (hs 
: s.Finite) : expGrowthInf (⨅ x in s, u x) = ⨅ x in s, expGrowthInf (u x)
参数：u : α -> Nat -> Real>=0∞；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_inf`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeInf α] [inst_1 : OrderTop α]   [inst_2 : SemilatticeInf
 β] …
· 使用定理 `InfTopHom.instInfTopHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Mi
n α] [inst_1 : Top α] [inst_2 : Min β] [inst_3 : Top β],   InfTopHomClass (InfTo
pHom α β) α β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ExpGrowth.expGrowthInf_inf`：expGrowthInf_inf : expGrowthInf (u ⊓ v) = ex
pGrowthInf u ⊓ expGrowthInf v
· 使用引理 `ExpGrowth.expGrowthInf_top`：expGrowthInf_top : expGrowthInf ⊤ = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.inf_eq_iInf`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] (s : Finset α) (f : α → β), s.inf f = ⨅ a ∈ s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
lemma expGrowthInf_biInf {α : Type*} (u : α → ℕ → ℝ≥0∞) {s : Set α} (hs : s.Finite) :
    expGrowthInf (⨅ x ∈ s, u x) = ⨅ x ∈ s, expGrowthInf (u x) := by
  have := map_finset_inf expGrowthInfTopHom hs.toFinset u
  simpa only [expGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]
/-
**ExpGrowth.expGrowthInf_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_iInf {ι : Type*} [Finite ι] (u : ι -> Nat -> Real>=0∞) : expG
rowthInf (⨅ i, u i) = ⨅ i, expGrowthInf (u i)
参数：u : ι -> Nat -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {f
 : β → α}, ⨅ x ∈ Set.univ, f x = ⨅ x, f x
· 使用引理 `ExpGrowth.expGrowthInf_biInf`：expGrowthInf_biInf {α : Type*} (u : α -> N
at -> Real>=0∞) {s : Set α} (hs : s.Finite) : expGrowthInf (⨅ x in s, u x) = ⨅ x
 in s, expGrowthIn…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma expGrowthInf_iInf {ι : Type*} [Finite ι] (u : ι → ℕ → ℝ≥0∞) :
    expGrowthInf (⨅ i, u i) = ⨅ i, expGrowthInf (u i) := by
  rw [← iInf_univ, expGrowthInf_biInf u Set.finite_univ, iInf_univ]
/-
**ExpGrowth.expGrowthSup_sup** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_sup : expGrowthSup (u ⊔ v) = expGrowthSup u ⊔ expGrowthSup v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExpGrowth.expGrowthSup.eq_1`：∀ (u : ℕ → ENNReal), ExpGrowth.expGrowthSup
 u = Filter.limsup (fun n => (u n).log / ↑n) Filter.atTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `limsup_max`：limsup_max [ConditionallyCompleteLinearOrder β] {f : Filter 
α} {u v : α -> β} (h₁ : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Pi.sup_apply`：sup_apply [forall i, Max (α' i)] (f g : forall i, α' i) (i
 : ι) : (f ⊔ g) i = f i ⊔ g i
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用定理 `ENNReal.log_monotone`：log_monotone : Monotone log
· 使用引理 `EReal.monotone_div_right_of_nonneg`：monotone_div_right_of_nonneg (h : 0 
<= b) : Monotone fun a => a / b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
-/
lemma expGrowthSup_sup : expGrowthSup (u ⊔ v) = expGrowthSup u ⊔ expGrowthSup v := by
  rw [expGrowthSup, expGrowthSup, expGrowthSup, ← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.sup_apply, log_monotone.map_max]
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

/-- Upper exponential growth as a `SupBotHom`. -/
/-
**ExpGrowth.expGrowthSupBotHom** 是 Mathlib 中的一个定义，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSupBotHom : SupBotHom (Nat -> Real>=0∞) EReal where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ExpGrowth.expGrowthSup_sup`：expGrowthSup_sup : expGrowthSup (u ⊔ v) = ex
pGrowthSup u ⊔ expGrowthSup v
· 使用引理 `ExpGrowth.expGrowthSup_zero`：expGrowthSup_zero : expGrowthSup 0 = ⊥

--- 原说明 ---
Upper exponential growth as a `SupBotHom`.
-/
noncomputable def expGrowthSupBotHom : SupBotHom (ℕ → ℝ≥0∞) EReal where
  toFun := expGrowthSup
  map_sup' _ _ := expGrowthSup_sup
  map_bot' := expGrowthSup_zero
/-
**ExpGrowth.expGrowthSup_biSup** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_biSup {α : Type*} (u : α -> Nat -> Real>=0∞) {s : Set α} (hs 
: s.Finite) : expGrowthSup (⨆ x in s, u x) = ⨆ x in s, expGrowthSup (u x)
参数：u : α -> Nat -> Real>=0∞；hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_sup`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeSup α] [inst_1 : OrderBot α]   [inst_2 : SemilatticeSup
 β] …
· 使用定理 `SupBotHom.instSupBotHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Ma
x α] [inst_1 : Bot α] [inst_2 : Max β] [inst_3 : Bot β],   SupBotHomClass (SupBo
tHom α β) α β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ExpGrowth.expGrowthSup_sup`：expGrowthSup_sup : expGrowthSup (u ⊔ v) = ex
pGrowthSup u ⊔ expGrowthSup v
· 使用引理 `ExpGrowth.expGrowthSup_zero`：expGrowthSup_zero : expGrowthSup 0 = ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
-/
lemma expGrowthSup_biSup {α : Type*} (u : α → ℕ → ℝ≥0∞) {s : Set α} (hs : s.Finite) :
    expGrowthSup (⨆ x ∈ s, u x) = ⨆ x ∈ s, expGrowthSup (u x) := by
  have := map_finset_sup expGrowthSupBotHom hs.toFinset u
  simpa only [expGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]
/-
**ExpGrowth.expGrowthSup_iSup** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_iSup {ι : Type*} [Finite ι] (u : ι -> Nat -> Real>=0∞) : expG
rowthSup (⨆ i, u i) = ⨆ i, expGrowthSup (u i)
参数：u : ι -> Nat -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_univ`：iSup_univ {f : β -> α} : ⨆ x in (univ : Set β), f x = ⨆ x, f 
x
· 使用引理 `ExpGrowth.expGrowthSup_biSup`：expGrowthSup_biSup {α : Type*} (u : α -> N
at -> Real>=0∞) {s : Set α} (hs : s.Finite) : expGrowthSup (⨆ x in s, u x) = ⨆ x
 in s, expGrowthSu…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma expGrowthSup_iSup {ι : Type*} [Finite ι] (u : ι → ℕ → ℝ≥0∞) :
    expGrowthSup (⨆ i, u i) = ⨆ i, expGrowthSup (u i) := by
  rw [← iSup_univ, expGrowthSup_biSup u Set.finite_univ, iSup_univ]

/-! ### Addition -/

/-
**ExpGrowth.le_expGrowthInf_add** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：le_expGrowthInf_add : expGrowthInf u ⊔ expGrowthInf v <= expGrowthInf (u +
 v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用引理 `ExpGrowth.expGrowthInf_monotone`：expGrowthInf_monotone : Monotone expGro
wthInf
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Pi.instCanonicallyOrderedAddForall`：∀ {ι : Type u_6} {Z : ι → Type u_7} 
[inst : (i : ι) → AddMonoid (Z i)] [inst_1 : (i : ι) → PartialOrder (Z i)]   [∀ 
(i : ι), CanonicallyOrde…
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a

--- 原说明 ---
### Addition
-/
lemma le_expGrowthInf_add : expGrowthInf u ⊔ expGrowthInf v ≤ expGrowthInf (u + v) :=
  sup_le (expGrowthInf_monotone le_self_add) (expGrowthInf_monotone le_add_self)
/-
**ExpGrowth.expGrowthSup_add** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_add : expGrowthSup (u + v) = expGrowthSup u ⊔ expGrowthSup v
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ExpGrowth.expGrowthSup_sup`：expGrowthSup_sup : expGrowthSup (u ⊔ v) = ex
pGrowthSup u ⊔ expGrowthSup v
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `ExpGrowth.expGrowthSup_le_of_eventually_le`：expGrowthSup_le_of_eventuall
y_le (hb : b != ∞) (h : forallᶠ n in atTop, u n <= b * v n) : expGrowthSup u <= 
expGrowthSup v
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `ENNReal.ofNat_ne_top`：ofNat_ne_top {n : Nat} [Nat.AtLeastTwo n] : ofNat(
n) != ∞
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Pi.sup_apply`：sup_apply [forall i, Max (α' i)] (f g : forall i, α' i) (i
 : ι) : (f ⊔ g) i = f i ⊔ g i
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用引理 `ExpGrowth.expGrowthSup_monotone`：expGrowthSup_monotone : Monotone expGro
wthSup
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
-/
lemma expGrowthSup_add : expGrowthSup (u + v) = expGrowthSup u ⊔ expGrowthSup v := by
  rw [← expGrowthSup_sup]
  apply le_antisymm
  · refine expGrowthSup_le_of_eventually_le (b := 2) ofNat_ne_top (Eventually.of_forall fun n ↦ ?_)
    rw [Pi.sup_apply u v n, Pi.add_apply u v n, two_mul]
    exact add_le_add (le_max_left (u n) (v n)) (le_max_right (u n) (v n))
  · refine expGrowthSup_monotone fun n ↦ ?_
    exact sup_le (self_le_add_right (u n) (v n)) (self_le_add_left (v n) (u n))

-- By lemma `expGrowthSup_add`, `expGrowthSup` is an `AddMonoidHom` from `ℕ → ℝ≥0∞` to
-- `Tropical ERealᵒᵈ`. Lemma `expGrowthSup_sum` is exactly `Finset.trop_inf`. We prove it from
-- scratch to reduce imports.
/-
**ExpGrowth.expGrowthSup_sum** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_sum {α : Type*} (u : α -> Nat -> Real>=0∞) (s : Finset α) : e
xpGrowthSup (∑ x in s, u x) = ⨆ x in s, expGrowthSup (u x)
参数：u : α -> Nat -> Real>=0∞；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.iSup_coe`：iSup_coe [SupSet β] (f : α -> β) (s : Finset α) : ⨆ x i
n (↑s : Set α), f x = ⨆ x in s, f x
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `iSup_emptyset`：iSup_emptyset {f : β -> α} : ⨆ x in (∅ : Set β), f x = ⊥
· 使用引理 `ExpGrowth.expGrowthSup_zero`：expGrowthSup_zero : expGrowthSup 0 = ⊥
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用引理 `ExpGrowth.expGrowthSup_add`：expGrowthSup_add : expGrowthSup (u + v) = ex
pGrowthSup u ⊔ expGrowthSup v
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `iSup_insert`：iSup_insert {f : β -> α} {s : Set β} {b : β} : ⨆ x in inser
t b s, f x = f b ⊔ ⨆ x in s, f x
-/
lemma expGrowthSup_sum {α : Type*} (u : α → ℕ → ℝ≥0∞) (s : Finset α) :
    expGrowthSup (∑ x ∈ s, u x) = ⨆ x ∈ s, expGrowthSup (u x) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, ← Finset.iSup_coe, Finset.coe_empty, iSup_emptyset,
    expGrowthSup_zero]
  | insert a t a_t ha => rw [Finset.sum_insert a_t, expGrowthSup_add, ← Finset.iSup_coe,
    Finset.coe_insert a t, iSup_insert, Finset.iSup_coe, ha]

end basic_properties

/-! ### Composition -/

section composition

variable {u : ℕ → ℝ≥0∞} {v : ℕ → ℕ}

/-
**ExpGrowth.le_expGrowthInf_comp** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：le_expGrowthInf_comp (hu : 1 <=ᶠ[atTop] u) (hv : Tendsto v atTop atTop) : 
(linearGrowthInf fun n => v n : EReal) * expGrowthInf u <= expGrowthInf (u ∘ v)
参数：hu : 1 <=ᶠ[atTop] u；hv : Tendsto v atTop atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearGrowth.le_linearGrowthInf_comp`：le_linearGrowthInf_comp (hu : 0 <=
ᶠ[atTop] u) (hv : Tendsto v atTop atTop) : (linearGrowthInf fun n => v n : EReal
) * linearGrowthInf u <= l…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `ENNReal.zero_le_log_iff`：∀ {x : ENNReal}, 0 ≤ x.log ↔ 1 ≤ x
· 使用引理 `Pi.one_apply`：one_apply (i : ι) : (1 : forall i, M i) i = 1
-/
lemma le_expGrowthInf_comp (hu : 1 ≤ᶠ[atTop] u) (hv : Tendsto v atTop atTop) :
    (linearGrowthInf fun n ↦ v n : EReal) * expGrowthInf u ≤ expGrowthInf (u ∘ v) := by
  apply le_linearGrowthInf_comp (hu.mono fun n h ↦ ?_) hv
  rw [Pi.one_apply] at h
  rwa [Pi.zero_apply, zero_le_log_iff]
/-
**ExpGrowth.expGrowthSup_comp_le** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_comp_le (hu : existsᶠ n in atTop, 1 <= u n) (hv₀ : (linearGro
wthSup fun n => v n : EReal) != 0) (hv₁ : (linearGrowthSup fun n => v n : EReal)
 != ⊤) (hv₂ : Tendsto v atTop atTop) : expGrowthSup (u ∘ v) <= (linearGrowthSup 
fun n => v n : EReal) * expGrowthSup u
参数：hu : existsᶠ n in atTop, 1 <= u n；hv₀ : (linearGrowthSup fun n => v n : EReal
) != 0；hv₁ : (linearGrowthSup fun n => v n : EReal) != ⊤；hv₂ : Tendsto v atTop a
tTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearGrowth.linearGrowthSup_comp_le`：linearGrowthSup_comp_le (hu : exis
tsᶠ n in atTop, 0 <= u n) (hv₀ : (linearGrowthSup fun n => v n : EReal) != 0) (h
v₁ : (linearGrowthSup fun …
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `ENNReal.zero_le_log_iff`：∀ {x : ENNReal}, 0 ≤ x.log ↔ 1 ≤ x
-/
lemma expGrowthSup_comp_le (hu : ∃ᶠ n in atTop, 1 ≤ u n)
    (hv₀ : (linearGrowthSup fun n ↦ v n : EReal) ≠ 0)
    (hv₁ : (linearGrowthSup fun n ↦ v n : EReal) ≠ ⊤) (hv₂ : Tendsto v atTop atTop) :
    expGrowthSup (u ∘ v) ≤ (linearGrowthSup fun n ↦ v n : EReal) * expGrowthSup u := by
  apply linearGrowthSup_comp_le (u := log ∘ u) (hu.mono fun n h ↦ ?_) hv₀ hv₁ hv₂
  rwa [comp_apply, zero_le_log_iff]

/-! ### Monotone sequences -/

/-
**ExpGrowth._root_.Monotone.expGrowthInf_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ExpGr
owth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Monotone sequences
-/
lemma _root_.Monotone.expGrowthInf_nonneg (h : Monotone u) (h' : u ≠ 0) :
    0 ≤ expGrowthInf u := by
  apply (log_monotone.comp h).linearGrowthInf_nonneg
  simp only [ne_eq, funext_iff, comp_apply, Pi.bot_apply, log_eq_bot_iff, Pi.zero_apply] at h' ⊢
  exact h'
/-
**ExpGrowth._root_.Monotone.expGrowthSup_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ExpGr
owth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.expGrowthSup_nonneg (h : Monotone u) (h' : u ≠ 0) :
    0 ≤ expGrowthSup u :=
  (h.expGrowthInf_nonneg h').trans expGrowthInf_le_expGrowthSup
/-
**ExpGrowth.expGrowthInf_comp_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthInf_comp_nonneg (h : Monotone u) (h' : u != 0) (hv : Tendsto v at
Top atTop) : 0 <= expGrowthInf (u ∘ v)
参数：h : Monotone u；h' : u != 0；hv : Tendsto v atTop atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearGrowth.linearGrowthInf_comp_nonneg`：linearGrowthInf_comp_nonneg (h
 : Monotone u) (h' : u != ⊥) (hv : Tendsto v atTop atTop) : 0 <= linearGrowthInf
 (u ∘ v)
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `ENNReal.log_monotone`：log_monotone : Monotone log
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
lemma expGrowthInf_comp_nonneg (h : Monotone u) (h' : u ≠ 0) (hv : Tendsto v atTop atTop) :
    0 ≤ expGrowthInf (u ∘ v) := by
  apply linearGrowthInf_comp_nonneg (u := log ∘ u) (log_monotone.comp h) _ hv
  simp only [ne_eq, funext_iff, comp_apply, Pi.bot_apply, log_eq_bot_iff, Pi.zero_apply] at h' ⊢
  exact h'
/-
**ExpGrowth.expGrowthSup_comp_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrowth`。
形式化陈述：expGrowthSup_comp_nonneg (h : Monotone u) (h' : u != 0) (hv : Tendsto v at
Top atTop) : 0 <= expGrowthSup (u ∘ v)
参数：h : Monotone u；h' : u != 0；hv : Tendsto v atTop atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ExpGrowth.expGrowthInf_comp_nonneg`：expGrowthInf_comp_nonneg (h : Monoto
ne u) (h' : u != 0) (hv : Tendsto v atTop atTop) : 0 <= expGrowthInf (u ∘ v)
· 使用引理 `ExpGrowth.expGrowthInf_le_expGrowthSup`：expGrowthInf_le_expGrowthSup : e
xpGrowthInf u <= expGrowthSup u
-/
lemma expGrowthSup_comp_nonneg (h : Monotone u) (h' : u ≠ 0) (hv : Tendsto v atTop atTop) :
    0 ≤ expGrowthSup (u ∘ v) :=
  (expGrowthInf_comp_nonneg h h' hv).trans expGrowthInf_le_expGrowthSup
/-
**ExpGrowth._root_.Monotone.expGrowthInf_comp_le** 是 Mathlib 中的一个引理，位于命名空间 `ExpG
rowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.expGrowthInf_comp_le (h : Monotone u)
    (hv₀ : (linearGrowthSup fun n ↦ v n : EReal) ≠ 0)
    (hv₁ : (linearGrowthSup fun n ↦ v n : EReal) ≠ ⊤) :
    expGrowthInf (u ∘ v) ≤ (linearGrowthSup fun n ↦ v n : EReal) * expGrowthInf u :=
  (log_monotone.comp h).linearGrowthInf_comp_le hv₀ hv₁
/-
**ExpGrowth._root_.Monotone.le_expGrowthSup_comp** 是 Mathlib 中的一个引理，位于命名空间 `ExpG
rowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.le_expGrowthSup_comp (h : Monotone u)
    (hv : (linearGrowthInf fun n ↦ v n : EReal) ≠ 0) :
    (linearGrowthInf fun n ↦ v n : EReal) * expGrowthSup u ≤ expGrowthSup (u ∘ v) :=
  (log_monotone.comp h).le_linearGrowthSup_comp hv
/-
**ExpGrowth._root_.Monotone.expGrowthInf_comp** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrow
th`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.expGrowthInf_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (𝓝 a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    expGrowthInf (u ∘ v) = a * expGrowthInf u :=
  (log_monotone.comp h).linearGrowthInf_comp hv ha ha'
/-
**ExpGrowth._root_.Monotone.expGrowthSup_comp** 是 Mathlib 中的一个引理，位于命名空间 `ExpGrow
th`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.expGrowthSup_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (𝓝 a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    expGrowthSup (u ∘ v) = a * expGrowthSup u :=
  (log_monotone.comp h).linearGrowthSup_comp hv ha ha'
/-
**ExpGrowth._root_.Monotone.expGrowthInf_comp_mul** 是 Mathlib 中的一个引理，位于命名空间 `Exp
Growth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.expGrowthInf_comp_mul {m : ℕ} (h : Monotone u) (hm : m ≠ 0) :
    expGrowthInf (fun n ↦ u (m * n)) = m * expGrowthInf u :=
  (log_monotone.comp h).linearGrowthInf_comp_mul hm
/-
**ExpGrowth._root_.Monotone.expGrowthSup_comp_mul** 是 Mathlib 中的一个引理，位于命名空间 `Exp
Growth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.expGrowthSup_comp_mul {m : ℕ} (h : Monotone u) (hm : m ≠ 0) :
    expGrowthSup (fun n ↦ u (m * n)) = m * expGrowthSup u :=
  (log_monotone.comp h).linearGrowthSup_comp_mul hm

end composition

end ExpGrowth

