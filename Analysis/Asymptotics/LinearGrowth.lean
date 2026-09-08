/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Linear growth

This file defines the linear growth of a sequence `u : ℕ → R`. This notion comes in two
versions, using a `liminf` and a `limsup` respectively. Most properties are developed for
`R = EReal`.

## Main definitions

- `linearGrowthInf`, `linearGrowthSup`: respectively, `liminf` and `limsup` of `(u n) / n`.
- `linearGrowthInfTopHom`, `linearGrowthSupBotHom`: the functions `linearGrowthInf`,
  `linearGrowthSup` as homomorphisms preserving finitary `Inf`/`Sup` respectively.

## TODO

Generalize statements from `EReal` to `ENNReal` (or others). This may need additional typeclasses.

Lemma about coercion from `ENNReal` to `EReal`. This needs additional lemmas about
`ENNReal.toEReal`.
-/

@[expose] public section

namespace LinearGrowth

open EReal Filter Function
open scoped Topology

/-! ### Definition -/

section definition

variable {R : Type*} [ConditionallyCompleteLattice R] [Div R] [NatCast R]

/-- Lower linear growth of a sequence. -/
/-
**LinearGrowth.linearGrowthInf** 是 Mathlib 中的一个定义，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf (u : Nat -> R) : R
参数：u : Nat -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lower linear growth of a sequence.
-/
noncomputable def linearGrowthInf (u : ℕ → R) : R := liminf (fun n ↦ u n / n) atTop

/-- Upper linear growth of a sequence. -/
/-
**LinearGrowth.linearGrowthSup** 是 Mathlib 中的一个定义，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup (u : Nat -> R) : R
参数：u : Nat -> R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Upper linear growth of a sequence.
-/
noncomputable def linearGrowthSup (u : ℕ → R) : R := limsup (fun n ↦ u n / n) atTop

end definition

/-! ### Basic properties -/

section basic_properties

variable {R : Type*} [ConditionallyCompleteLattice R] [Div R] [NatCast R] {u v : ℕ → R}

/-
**LinearGrowth.linearGrowthInf_congr** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_congr (h : u =ᶠ[atTop] v) : linearGrowthInf u = linearGrow
thInf v
参数：h : u =ᶠ[atTop] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_congr`：liminf_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : liminf u 
f = limin…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
lemma linearGrowthInf_congr (h : u =ᶠ[atTop] v) :
    linearGrowthInf u = linearGrowthInf v :=
  liminf_congr (h.mono fun _ uv ↦ uv ▸ rfl)
/-
**LinearGrowth.linearGrowthSup_congr** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_congr (h : u =ᶠ[atTop] v) : linearGrowthSup u = linearGrow
thSup v
参数：h : u =ᶠ[atTop] v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
-/
lemma linearGrowthSup_congr (h : u =ᶠ[atTop] v) :
    linearGrowthSup u = linearGrowthSup v :=
  limsup_congr (h.mono fun _ uv ↦ uv ▸ rfl)
/-
**LinearGrowth.linearGrowthInf_le_linearGrowthSup** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earGrowth`。
形式化陈述：linearGrowthInf_le_linearGrowthSup (h : IsBoundedUnder (· <= ·) atTop fun 
n => u n / n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.liminf_le_limsup`：liminf_le_limsup {f : Filter β} [NeBot f] {u : 
β -> α} (h : f.IsBoundedUnder (· <= ·) u
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma linearGrowthInf_le_linearGrowthSup
    (h : IsBoundedUnder (· ≤ ·) atTop fun n ↦ u n / n := by isBoundedDefault)
    (h' : IsBoundedUnder (· ≥ ·) atTop fun n ↦ u n / n := by isBoundedDefault) :
    linearGrowthInf u ≤ linearGrowthSup u :=
  liminf_le_limsup h h'

end basic_properties

section basic_properties

variable {u v : ℕ → EReal} {a b : EReal}

/-
**LinearGrowth.linearGrowthInf_eventually_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearGrowth`。
形式化陈述：linearGrowthInf_eventually_monotone (h : u <=ᶠ[atTop] v) : linearGrowthInf
 u <= linearGrowthInf v
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
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
-/
lemma linearGrowthInf_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    linearGrowthInf u ≤ linearGrowthInf v :=
  liminf_le_liminf (h.mono fun n u_v ↦ EReal.monotone_div_right_of_nonneg n.cast_nonneg' u_v)
/-
**LinearGrowth.linearGrowthInf_monotone** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`
。
形式化陈述：linearGrowthInf_monotone (h : u <= v) : linearGrowthInf u <= linearGrowthI
nf v
参数：h : u <= v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearGrowth.linearGrowthInf_eventually_monotone`：linearGrowthInf_eventu
ally_monotone (h : u <=ᶠ[atTop] v) : linearGrowthInf u <= linearGrowthInf v
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma linearGrowthInf_monotone (h : u ≤ v) : linearGrowthInf u ≤ linearGrowthInf v :=
  linearGrowthInf_eventually_monotone (Eventually.of_forall h)
/-
**LinearGrowth.linearGrowthSup_eventually_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearGrowth`。
形式化陈述：linearGrowthSup_eventually_monotone (h : u <=ᶠ[atTop] v) : linearGrowthSup
 u <= linearGrowthSup v
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
· 使用定理 `Filter.isCobounded_le_of_bot`：isCobounded_le_of_bot [LE α] [OrderBot α] 
{f : Filter α} : f.IsCobounded (· <= ·)
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
-/
lemma linearGrowthSup_eventually_monotone (h : u ≤ᶠ[atTop] v) :
    linearGrowthSup u ≤ linearGrowthSup v :=
  limsup_le_limsup (h.mono fun n u_v ↦ monotone_div_right_of_nonneg n.cast_nonneg' u_v)
/-
**LinearGrowth.linearGrowthSup_monotone** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`
。
形式化陈述：linearGrowthSup_monotone (h : u <= v) : linearGrowthSup u <= linearGrowthS
up v
参数：h : u <= v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearGrowth.linearGrowthSup_eventually_monotone`：linearGrowthSup_eventu
ally_monotone (h : u <=ᶠ[atTop] v) : linearGrowthSup u <= linearGrowthSup v
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma linearGrowthSup_monotone (h : u ≤ v) : linearGrowthSup u ≤ linearGrowthSup v :=
  linearGrowthSup_eventually_monotone (Eventually.of_forall h)
/-
**LinearGrowth.linearGrowthInf_le_linearGrowthSup_of_frequently_le** 是 Mathlib 中
的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_le_linearGrowthSup_of_frequently_le (h : existsᶠ n in atTo
p, u n <= v n) : linearGrowthInf u <= linearGrowthSup v
参数：h : existsᶠ n in atTop, u n <= v n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.liminf_le_limsup_of_frequently_le`：liminf_le_limsup_of_frequently
_le {v : α -> β} (h : existsᶠ x in f, u x <= v x) (h₁ : f.IsBoundedUnder (· >= ·
) u
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用引理 `EReal.div_le_div_right_of_nonneg`：div_le_div_right_of_nonneg (h : 0 <= c
) (h' : a <= b) : a / c <= b / c
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
-/
lemma linearGrowthInf_le_linearGrowthSup_of_frequently_le (h : ∃ᶠ n in atTop, u n ≤ v n) :
    linearGrowthInf u ≤ linearGrowthSup v :=
  (liminf_le_limsup_of_frequently_le) <| h.mono fun n u_v ↦ by gcongr
/-
**LinearGrowth.linearGrowthInf_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_le_iff : linearGrowthInf u <= a ↔ forall b > a, existsᶠ n 
: Nat in atTop, u n <= b * n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearGrowth.linearGrowthInf.eq_1`：∀ {R : Type u_1} [inst : Conditionall
yCompleteLattice R] [inst_1 : Div R] [inst_2 : NatCast R] (u : ℕ → R),   LinearG
rowth.linearGrowthInf u…
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
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma linearGrowthInf_le_iff :
    linearGrowthInf u ≤ a ↔ ∀ b > a, ∃ᶠ n : ℕ in atTop, u n ≤ b * n := by
  rw [linearGrowthInf, liminf_le_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), mul_comm _ b]
/-
**LinearGrowth.le_linearGrowthInf_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：le_linearGrowthInf_iff : a <= linearGrowthInf u ↔ forall b < a, forallᶠ n 
: Nat in atTop, b * n <= u n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearGrowth.linearGrowthInf.eq_1`：∀ {R : Type u_1} [inst : Conditionall
yCompleteLattice R] [inst_1 : Div R] [inst_2 : NatCast R] (u : ℕ → R),   LinearG
rowth.linearGrowthInf u…
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
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_linearGrowthInf_iff :
    a ≤ linearGrowthInf u ↔ ∀ b < a, ∀ᶠ n : ℕ in atTop, b * n ≤ u n := by
  rw [linearGrowthInf, le_liminf_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]
/-
**LinearGrowth.linearGrowthSup_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_le_iff : linearGrowthSup u <= a ↔ forall b > a, forallᶠ n 
: Nat in atTop, u n <= b * n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearGrowth.linearGrowthSup.eq_1`：∀ {R : Type u_1} [inst : Conditionall
yCompleteLattice R] [inst_1 : Div R] [inst_2 : NatCast R] (u : ℕ → R),   LinearG
rowth.linearGrowthSup u…
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
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma linearGrowthSup_le_iff :
    linearGrowthSup u ≤ a ↔ ∀ b > a, ∀ᶠ n : ℕ in atTop, u n ≤ b * n := by
  rw [linearGrowthSup, limsup_le_iff']
  refine forall₂_congr fun b _ ↦ eventually_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  rw [div_le_iff_le_mul (by norm_cast) (natCast_ne_top n), mul_comm _ b]
/-
**LinearGrowth.le_linearGrowthSup_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：le_linearGrowthSup_iff : a <= linearGrowthSup u ↔ forall b < a, existsᶠ n 
: Nat in atTop, b * n <= u n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearGrowth.linearGrowthSup.eq_1`：∀ {R : Type u_1} [inst : Conditionall
yCompleteLattice R] [inst_1 : Div R] [inst_2 : NatCast R] (u : ℕ → R),   LinearG
rowth.linearGrowthSup u…
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
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_linearGrowthSup_iff :
    a ≤ linearGrowthSup u ↔ ∀ b < a, ∃ᶠ n : ℕ in atTop, b * n ≤ u n := by
  rw [linearGrowthSup, le_limsup_iff']
  refine forall₂_congr fun b _ ↦ frequently_congr (eventually_atTop.2 ⟨1, fun n _ ↦ ?_⟩)
  nth_rw 1 [le_div_iff_mul_le (by norm_cast) (natCast_ne_top n)]

/- Forward direction of `linearGrowthInf_le_iff`. -/
/-
**LinearGrowth.frequently_le_mul** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：frequently_le_mul (h : linearGrowthInf u < a) : existsᶠ n : Nat in atTop, 
u n <= a * n
参数：h : linearGrowthInf u < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LinearGrowth.linearGrowthInf_le_iff`：linearGrowthInf_le_iff : linearGrow
thInf u <= a ↔ forall b > a, existsᶠ n : Nat in atTop, u n <= b * n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Forward direction of `linearGrowthInf_le_iff`.
-/
lemma frequently_le_mul (h : linearGrowthInf u < a) :
    ∃ᶠ n : ℕ in atTop, u n ≤ a * n :=
  linearGrowthInf_le_iff.1 (le_refl (linearGrowthInf u)) a h

/- Forward direction of `le_linearGrowthInf_iff`. -/
/-
**LinearGrowth.eventually_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：eventually_mul_le (h : a < linearGrowthInf u) : forallᶠ n : Nat in atTop, 
a * n <= u n
参数：h : a < linearGrowthInf u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LinearGrowth.le_linearGrowthInf_iff`：le_linearGrowthInf_iff : a <= linea
rGrowthInf u ↔ forall b < a, forallᶠ n : Nat in atTop, b * n <= u n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Forward direction of `le_linearGrowthInf_iff`.
-/
lemma eventually_mul_le (h : a < linearGrowthInf u) :
    ∀ᶠ n : ℕ in atTop, a * n ≤ u n :=
  le_linearGrowthInf_iff.1 (le_refl (linearGrowthInf u)) a h

/- Forward direction of `linearGrowthSup_le_iff`. -/
/-
**LinearGrowth.eventually_le_mul** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：eventually_le_mul (h : linearGrowthSup u < a) : forallᶠ n : Nat in atTop, 
u n <= a * n
参数：h : linearGrowthSup u < a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LinearGrowth.linearGrowthSup_le_iff`：linearGrowthSup_le_iff : linearGrow
thSup u <= a ↔ forall b > a, forallᶠ n : Nat in atTop, u n <= b * n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Forward direction of `linearGrowthSup_le_iff`.
-/
lemma eventually_le_mul (h : linearGrowthSup u < a) :
    ∀ᶠ n : ℕ in atTop, u n ≤ a * n :=
  linearGrowthSup_le_iff.1 (le_refl (linearGrowthSup u)) a h

/- Forward direction of `le_linearGrowthSup_iff`. -/
/-
**LinearGrowth.frequently_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：frequently_mul_le (h : a < linearGrowthSup u) : existsᶠ n : Nat in atTop, 
a * n <= u n
参数：h : a < linearGrowthSup u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LinearGrowth.le_linearGrowthSup_iff`：le_linearGrowthSup_iff : a <= linea
rGrowthSup u ↔ forall b < a, existsᶠ n : Nat in atTop, b * n <= u n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Forward direction of `le_linearGrowthSup_iff`.
-/
lemma frequently_mul_le (h : a < linearGrowthSup u) :
    ∃ᶠ n : ℕ in atTop, a * n ≤ u n :=
  le_linearGrowthSup_iff.1 (le_refl (linearGrowthSup u)) a h
/-
**LinearGrowth._root_.Frequently.linearGrowthInf_le** 是 Mathlib 中的一个引理，位于命名空间 `L
inearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Frequently.linearGrowthInf_le (h : ∃ᶠ n : ℕ in atTop, u n ≤ a * n) :
    linearGrowthInf u ≤ a :=
  linearGrowthInf_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans <| by gcongr
/-
**LinearGrowth._root_.Eventually.le_linearGrowthInf** 是 Mathlib 中的一个引理，位于命名空间 `L
inearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Eventually.le_linearGrowthInf (h : ∀ᶠ n : ℕ in atTop, a * n ≤ u n) :
    a ≤ linearGrowthInf u :=
  le_linearGrowthInf_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' <| by gcongr
/-
**LinearGrowth._root_.Eventually.linearGrowthSup_le** 是 Mathlib 中的一个引理，位于命名空间 `L
inearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Eventually.linearGrowthSup_le (h : ∀ᶠ n : ℕ in atTop, u n ≤ a * n) :
    linearGrowthSup u ≤ a :=
  linearGrowthSup_le_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans <| by gcongr
/-
**LinearGrowth._root_.Frequently.le_linearGrowthSup** 是 Mathlib 中的一个引理，位于命名空间 `L
inearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Frequently.le_linearGrowthSup (h : ∃ᶠ n : ℕ in atTop, a * n ≤ u n) :
    a ≤ linearGrowthSup u :=
  le_linearGrowthSup_iff.2 fun c c_u ↦ h.mono fun n hn ↦ hn.trans' <| by gcongr

/-! ### Special cases -/

/-
**LinearGrowth.linearGrowthSup_bot** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_bot : linearGrowthSup (⊥ : Nat -> EReal) = (⊥ : EReal)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用引理 `EReal.bot_div_of_pos_ne_top`：bot_div_of_pos_ne_top {a : EReal} (h : 0 < 
a) (h' : a != ⊤) : ⊥ / a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `EReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : EReal) != ⊤

--- 原说明 ---
### Special cases
-/
lemma linearGrowthSup_bot : linearGrowthSup (⊥ : ℕ → EReal) = (⊥ : EReal) := by
  nth_rw 2 [← limsup_const (f := atTop (α := ℕ)) ⊥]
  refine limsup_congr <| (eventually_gt_atTop 0).mono fun n n_pos ↦ ?_
  exact bot_div_of_pos_ne_top (by positivity) (natCast_ne_top n)
/-
**LinearGrowth.linearGrowthInf_bot** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_bot : linearGrowthInf (⊥ : Nat -> EReal) = (⊥ : EReal)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearGrowth.linearGrowthSup_bot`：linearGrowthSup_bot : linearGrowthSup 
(⊥ : Nat -> EReal) = (⊥ : EReal)
· 使用引理 `LinearGrowth.linearGrowthInf_le_linearGrowthSup`：linearGrowthInf_le_line
arGrowthSup (h : IsBoundedUnder (· <= ·) atTop fun n => u n / n
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
-/
lemma linearGrowthInf_bot : linearGrowthInf (⊥ : ℕ → EReal) = (⊥ : EReal) := by
  apply le_bot_iff.1
  rw [← linearGrowthSup_bot]
  exact linearGrowthInf_le_linearGrowthSup
/-
**LinearGrowth.linearGrowthInf_top** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_top : linearGrowthInf ⊤ = (⊤ : EReal)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用引理 `EReal.top_div_of_pos_ne_top`：top_div_of_pos_ne_top {a : EReal} (h : 0 < 
a) (h' : a != ⊤) : ⊤ / a = ⊤
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `EReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : EReal) != ⊤
-/
lemma linearGrowthInf_top : linearGrowthInf ⊤ = (⊤ : EReal) := by
  nth_rw 2 [← liminf_const (f := atTop (α := ℕ)) ⊤]
  refine liminf_congr (eventually_atTop.2 ?_)
  exact ⟨1, fun n n_pos ↦ top_div_of_pos_ne_top (Nat.cast_pos'.2 n_pos) (natCast_ne_top n)⟩
/-
**LinearGrowth.linearGrowthSup_top** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_top : linearGrowthSup (⊤ : Nat -> EReal) = (⊤ : EReal)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearGrowth.linearGrowthInf_top`：linearGrowthInf_top : linearGrowthInf 
⊤ = (⊤ : EReal)
· 使用引理 `LinearGrowth.linearGrowthInf_le_linearGrowthSup`：linearGrowthInf_le_line
arGrowthSup (h : IsBoundedUnder (· <= ·) atTop fun n => u n / n
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
-/
lemma linearGrowthSup_top : linearGrowthSup (⊤ : ℕ → EReal) = (⊤ : EReal) := by
  apply top_le_iff.1
  rw [← linearGrowthInf_top]
  exact linearGrowthInf_le_linearGrowthSup
/-
**LinearGrowth.linearGrowthInf_const** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_const (h : b != ⊥) (h' : b != ⊤) : linearGrowthInf (fun _ 
=> b) = 0
参数：h : b != ⊥；h' : b != ⊤。
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
-/
lemma linearGrowthInf_const (h : b ≠ ⊥) (h' : b ≠ ⊤) : linearGrowthInf (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat h h').liminf_eq
/-
**LinearGrowth.linearGrowthSup_const** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_const (h : b != ⊥) (h' : b != ⊤) : linearGrowthSup (fun _ 
=> b) = 0
参数：h : b != ⊥；h' : b != ⊤。
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
-/
lemma linearGrowthSup_const (h : b ≠ ⊥) (h' : b ≠ ⊤) : linearGrowthSup (fun _ ↦ b) = 0 :=
  (tendsto_const_div_atTop_nhds_zero_nat h h').limsup_eq
/-
**LinearGrowth.linearGrowthInf_zero** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_zero : linearGrowthInf 0 = (0 : EReal)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearGrowth.linearGrowthInf_const`：linearGrowthInf_const (h : b != ⊥) (
h' : b != ⊤) : linearGrowthInf (fun _ => b) = 0
· 使用定理 `EReal.zero_ne_bot`：zero_ne_bot : (0 : EReal) != ⊥
· 使用定理 `EReal.zero_ne_top`：zero_ne_top : (0 : EReal) != ⊤
-/
lemma linearGrowthInf_zero : linearGrowthInf 0 = (0 : EReal) :=
  linearGrowthInf_const zero_ne_bot zero_ne_top
/-
**LinearGrowth.linearGrowthSup_zero** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_zero : linearGrowthSup 0 = (0 : EReal)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearGrowth.linearGrowthSup_const`：linearGrowthSup_const (h : b != ⊥) (
h' : b != ⊤) : linearGrowthSup (fun _ => b) = 0
· 使用定理 `EReal.zero_ne_bot`：zero_ne_bot : (0 : EReal) != ⊥
· 使用定理 `EReal.zero_ne_top`：zero_ne_top : (0 : EReal) != ⊤
-/
lemma linearGrowthSup_zero : linearGrowthSup 0 = (0 : EReal) :=
  linearGrowthSup_const zero_ne_bot zero_ne_top
/-
**LinearGrowth.linearGrowthInf_const_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `LinearG
rowth`。
形式化陈述：linearGrowthInf_const_mul_self : linearGrowthInf (fun n => a * n) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Frequently.linearGrowthInf_le`：∀ {u : ℕ → EReal} {a : EReal}, (∃ᶠ (n : ℕ
) in Filter.atTop, u n ≤ a * ↑n) → LinearGrowth.linearGrowthInf u ≤ a
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eventually.le_linearGrowthInf`：∀ {u : ℕ → EReal} {a : EReal}, (∀ᶠ (n : ℕ
) in Filter.atTop, a * ↑n ≤ u n) → a ≤ LinearGrowth.linearGrowthInf u
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
lemma linearGrowthInf_const_mul_self : linearGrowthInf (fun n ↦ a * n) = a :=
  le_antisymm (Frequently.linearGrowthInf_le (Frequently.of_forall fun _ ↦ le_refl _))
    (Eventually.le_linearGrowthInf (Eventually.of_forall fun _ ↦ le_refl _))
/-
**LinearGrowth.linearGrowthSup_const_mul_self** 是 Mathlib 中的一个引理，位于命名空间 `LinearG
rowth`。
形式化陈述：linearGrowthSup_const_mul_self : linearGrowthSup (fun n => a * n) = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eventually.linearGrowthSup_le`：∀ {u : ℕ → EReal} {a : EReal}, (∀ᶠ (n : ℕ
) in Filter.atTop, u n ≤ a * ↑n) → LinearGrowth.linearGrowthSup u ≤ a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Frequently.le_linearGrowthSup`：∀ {u : ℕ → EReal} {a : EReal}, (∃ᶠ (n : ℕ
) in Filter.atTop, a * ↑n ≤ u n) → a ≤ LinearGrowth.linearGrowthSup u
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma linearGrowthSup_const_mul_self : linearGrowthSup (fun n ↦ a * n) = a :=
  le_antisymm (Eventually.linearGrowthSup_le (Eventually.of_forall fun _ ↦ le_refl _))
    (Frequently.le_linearGrowthSup (Frequently.of_forall fun _ ↦ le_refl _))
/-
**LinearGrowth.linearGrowthInf_natCast_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `LinearG
rowth`。
形式化陈述：linearGrowthInf_natCast_nonneg (v : Nat -> Nat) : 0 <= linearGrowthInf fun
 n => (v n : EReal)
参数：v : Nat -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.le_liminf_of_le`：le_liminf_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.isCobounded_ge_of_top`：∀ {α : Type u_1} [inst : LE α] [OrderTop α
] {f : Filter α}, Filter.IsCobounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `EReal.div_nonneg`：div_nonneg (h : 0 <= a) (h' : 0 <= b) : 0 <= a / b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
-/
lemma linearGrowthInf_natCast_nonneg (v : ℕ → ℕ) :
    0 ≤ linearGrowthInf fun n ↦ (v n : EReal) :=
  (le_liminf_of_le) (Eventually.of_forall fun n ↦ div_nonneg (v n).cast_nonneg' n.cast_nonneg')
/-
**LinearGrowth.tendsto_atTop_of_linearGrowthInf_pos** 是 Mathlib 中的一个引理，位于命名空间 `L
inearGrowth`。
形式化陈述：tendsto_atTop_of_linearGrowthInf_pos (h : 0 < linearGrowthInf u) : Tendsto
 u atTop (𝓝 ⊤)
参数：h : 0 < linearGrowthInf u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `instDenselyOrderedEReal`：DenselyOrdered EReal
· 使用定理 `tendsto_nhds_top_mono`：tendsto_nhds_top_mono [TopologicalSpace β] [Preor
der β] [OrderTop β] [OrderTopology β] {l : Filter α} {f g : α -> β} (hf : Tendst
o f l (𝓝 ⊤)…
· 使用定理 `EReal.instOrderTopology`：OrderTopology EReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `EReal.tendsto_nhds_top_iff_real`：tendsto_nhds_top_iff_real {α : Type*} {
m : α -> EReal} {f : Filter α} : Tendsto m f (𝓝 ⊤) ↔ forall x : Real, forallᶠ a 
in f, ↑x < m a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `ne_top_of_lt`：ne_top_of_lt (h : a < b) : a != ⊤
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `exists_nat_ge`：exists_nat_ge (x : R) : exists n : Nat, x <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EReal.coe_coe_eq_natCast`：coe_coe_eq_natCast (n : Nat) : (n : Real) = (n
 : EReal)
· 使用定理 `EReal.coe_mul`：coe_mul (x y : Real) : (↑(x * y) : EReal) = x * y
· 使用定理 `EReal.coe_lt_coe_iff`：∀ {x y : ℝ}, ↑x < ↑y ↔ x < y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `EReal.coe_pos`：∀ {x : ℝ}, 0 < ↑x ↔ 0 < x
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.cast_lt`：cast_lt : (m : α) < n ↔ m < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 33 条，此处仅展示前 30 条）
-/
lemma tendsto_atTop_of_linearGrowthInf_pos (h : 0 < linearGrowthInf u) :
    Tendsto u atTop (𝓝 ⊤) := by
  obtain ⟨a, a_0, a_v⟩ := exists_between h
  apply tendsto_nhds_top_mono _ ((le_linearGrowthInf_iff (u := u)).1 (le_refl _) a a_v)
  refine tendsto_nhds_top_iff_real.2 fun M ↦ eventually_atTop.2 ?_
  lift a to ℝ using ⟨ne_top_of_lt a_v, ne_bot_of_gt a_0⟩
  rw [EReal.coe_pos] at a_0
  obtain ⟨n, hn⟩ := exists_nat_ge (M / a)
  refine ⟨n + 1, fun k k_n ↦ ?_⟩
  rw [← coe_coe_eq_natCast, ← coe_mul, EReal.coe_lt_coe_iff, mul_comm]
  exact (div_lt_iff₀ a_0).1 (hn.trans_lt (Nat.cast_lt.2 k_n))

/-! ### Addition and negation -/

/-
**LinearGrowth.le_linearGrowthInf_add** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：le_linearGrowthInf_add : linearGrowthInf u + linearGrowthInf v <= linearGr
owthInf (u + v)
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.add_div_of_nonneg_right`：add_div_of_nonneg_right (h : 0 <= c) : (a
 + b) / c = a / c + b / c
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal

--- 原说明 ---
### Addition and negation
-/
lemma le_linearGrowthInf_add :
    linearGrowthInf u + linearGrowthInf v ≤ linearGrowthInf (u + v) := by
  refine le_liminf_add.trans_eq (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, ← add_div_of_nonneg_right n.cast_nonneg']

/-- See `linearGrowthInf_add_le'` for a version with swapped argument `u` and `v`. -/
/-
**LinearGrowth.linearGrowthInf_add_le** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_add_le (h : linearGrowthSup u != ⊥ ∨ linearGrowthInf v != 
⊤) (h' : linearGrowthSup u != ⊤ ∨ linearGrowthInf v != ⊥) : linearGrowthInf (u +
 v) <= linearGrowthSup u + linearGrowthInf v
参数：h : linearGrowthSup u != ⊥ ∨ linearGrowthInf v != ⊤；h' : linearGrowthSup u !=
 ⊤ ∨ linearGrowthInf v != ⊥。
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.add_div_of_nonneg_right`：add_div_of_nonneg_right (h : 0 <= c) : (a
 + b) / c = a / c + b / c
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal

--- 原说明 ---
See `linearGrowthInf_add_le'` for a version with swapped argument `u` and `v`.
-/
lemma linearGrowthInf_add_le (h : linearGrowthSup u ≠ ⊥ ∨ linearGrowthInf v ≠ ⊤)
    (h' : linearGrowthSup u ≠ ⊤ ∨ linearGrowthInf v ≠ ⊥) :
    linearGrowthInf (u + v) ≤ linearGrowthSup u + linearGrowthInf v := by
  refine (liminf_add_le h h').trans_eq' (liminf_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, ← add_div_of_nonneg_right n.cast_nonneg']

/-- See `linearGrowthInf_add_le` for a version with swapped argument `u` and `v`. -/
/-
**LinearGrowth.linearGrowthInf_add_le'** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_add_le' (h : linearGrowthInf u != ⊥ ∨ linearGrowthSup v !=
 ⊤) (h' : linearGrowthInf u != ⊤ ∨ linearGrowthSup v != ⊥) : linearGrowthInf (u 
+ v) <= linearGrowthInf u + linearGrowthSup v
参数：h : linearGrowthInf u != ⊥ ∨ linearGrowthSup v != ⊤；h' : linearGrowthInf u !=
 ⊤ ∨ linearGrowthSup v != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `LinearGrowth.linearGrowthInf_add_le`：linearGrowthInf_add_le (h : linearG
rowthSup u != ⊥ ∨ linearGrowthInf v != ⊤) (h' : linearGrowthSup u != ⊤ ∨ linearG
rowthInf v != ⊥) : linear…
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a

--- 原说明 ---
See `linearGrowthInf_add_le` for a version with swapped argument `u` and `v`.
-/
lemma linearGrowthInf_add_le' (h : linearGrowthInf u ≠ ⊥ ∨ linearGrowthSup v ≠ ⊤)
    (h' : linearGrowthInf u ≠ ⊤ ∨ linearGrowthSup v ≠ ⊥) :
    linearGrowthInf (u + v) ≤ linearGrowthInf u + linearGrowthSup v := by
  rw [add_comm u v, add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact linearGrowthInf_add_le h'.symm h.symm

/-- See `le_linearGrowthSup_add'` for a version with swapped argument `u` and `v`. -/
/-
**LinearGrowth.le_linearGrowthSup_add** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：le_linearGrowthSup_add : linearGrowthSup u + linearGrowthInf v <= linearGr
owthSup (u + v)
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
· 使用引理 `EReal.add_div_of_nonneg_right`：add_div_of_nonneg_right (h : 0 <= c) : (a
 + b) / c = a / c + b / c
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal

--- 原说明 ---
See `le_linearGrowthSup_add'` for a version with swapped argument `u` and `v`.
-/
lemma le_linearGrowthSup_add : linearGrowthSup u + linearGrowthInf v ≤ linearGrowthSup (u + v) := by
  refine le_limsup_add.trans_eq (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, add_div_of_nonneg_right n.cast_nonneg']

/-- See `le_linearGrowthSup_add` for a version with swapped argument `u` and `v`. -/
/-
**LinearGrowth.le_linearGrowthSup_add'** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：le_linearGrowthSup_add' : linearGrowthInf u + linearGrowthSup v <= linearG
rowthSup (u + v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `LinearGrowth.le_linearGrowthSup_add`：le_linearGrowthSup_add : linearGrow
thSup u + linearGrowthInf v <= linearGrowthSup (u + v)

--- 原说明 ---
See `le_linearGrowthSup_add` for a version with swapped argument `u` and `v`.
-/
lemma le_linearGrowthSup_add' :
    linearGrowthInf u + linearGrowthSup v ≤ linearGrowthSup (u + v) := by
  rw [add_comm u v, add_comm (linearGrowthInf u) (linearGrowthSup v)]
  exact le_linearGrowthSup_add
/-
**LinearGrowth.linearGrowthSup_add_le** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_add_le (h : linearGrowthSup u != ⊥ ∨ linearGrowthSup v != 
⊤) (h' : linearGrowthSup u != ⊤ ∨ linearGrowthSup v != ⊥) : linearGrowthSup (u +
 v) <= linearGrowthSup u + linearGrowthSup v
参数：h : linearGrowthSup u != ⊥ ∨ linearGrowthSup v != ⊤；h' : linearGrowthSup u !=
 ⊤ ∨ linearGrowthSup v != ⊥。
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
· 使用引理 `EReal.add_div_of_nonneg_right`：add_div_of_nonneg_right (h : 0 <= c) : (a
 + b) / c = a / c + b / c
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
-/
lemma linearGrowthSup_add_le (h : linearGrowthSup u ≠ ⊥ ∨ linearGrowthSup v ≠ ⊤)
    (h' : linearGrowthSup u ≠ ⊤ ∨ linearGrowthSup v ≠ ⊥) :
    linearGrowthSup (u + v) ≤ linearGrowthSup u + linearGrowthSup v := by
  refine (limsup_add_le h h').trans_eq' (limsup_congr (Eventually.of_forall fun n ↦ ?_))
  rw [Pi.add_apply, Pi.add_apply, add_div_of_nonneg_right n.cast_nonneg']
/-
**LinearGrowth.linearGrowthInf_neg** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_neg : linearGrowthInf (-u) = - linearGrowthSup u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearGrowth.linearGrowthSup.eq_1`：∀ {R : Type u_1} [inst : Conditionall
yCompleteLattice R] [inst_1 : Div R] [inst_2 : NatCast R] (u : ℕ → R),   LinearG
rowth.linearGrowthSup u…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.liminf_neg`：liminf_neg : liminf (-v) f = -limsup v f
· 使用定理 `Filter.liminf_congr`：liminf_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : liminf u 
f = limin…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
lemma linearGrowthInf_neg : linearGrowthInf (-u) = - linearGrowthSup u := by
  rw [linearGrowthSup, ← liminf_neg]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.neg_apply, div_eq_mul_inv, div_eq_mul_inv, ← neg_mul]
/-
**LinearGrowth.linearGrowthSup_inv** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_inv : linearGrowthSup (-u) = - linearGrowthInf u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearGrowth.linearGrowthInf.eq_1`：∀ {R : Type u_1} [inst : Conditionall
yCompleteLattice R] [inst_1 : Div R] [inst_2 : NatCast R] (u : ℕ → R),   LinearG
rowth.linearGrowthInf u…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.limsup_neg`：limsup_neg : limsup (-v) f = -liminf v f
· 使用定理 `Filter.limsup_congr`：limsup_congr {α : Type*} [ConditionallyCompleteLatt
ice β] {f : Filter α} {u v : α -> β} (h : forallᶠ a in f, u a = v a) : limsup u 
f = limsu…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
lemma linearGrowthSup_inv : linearGrowthSup (-u) = - linearGrowthInf u := by
  rw [linearGrowthInf, ← limsup_neg]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  rw [Pi.neg_apply, Pi.neg_apply, div_eq_mul_inv, div_eq_mul_inv, ← neg_mul]

/-! ### Affine bounds -/

/-
**LinearGrowth.linearGrowthInf_le_of_eventually_le** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearGrowth`。
形式化陈述：linearGrowthInf_le_of_eventually_le (hb : b != ⊤) (h : forallᶠ n in atTop,
 u n <= v n + b) : linearGrowthInf u <= linearGrowthInf v
参数：hb : b != ⊤；h : forallᶠ n in atTop, u n <= v n + b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `LinearGrowth.linearGrowthInf_eventually_monotone`：linearGrowthInf_eventu
ally_monotone (h : u <=ᶠ[atTop] v) : linearGrowthInf u <= linearGrowthInf v
· 使用定理 `eq_bot_or_bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Order
Bot α] (a : α), a = ⊥ ∨ ⊥ < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用引理 `LinearGrowth.linearGrowthInf_bot`：linearGrowthInf_bot : linearGrowthInf 
(⊥ : Nat -> EReal) = (⊥ : EReal)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `LinearGrowth.linearGrowthInf_add_le'`：linearGrowthInf_add_le' (h : linea
rGrowthInf u != ⊥ ∨ linearGrowthSup v != ⊤) (h' : linearGrowthInf u != ⊤ ∨ linea
rGrowthSup v != ⊥) : linea…
· 使用引理 `LinearGrowth.linearGrowthSup_const`：linearGrowthSup_const (h : b != ⊥) (
h' : b != ⊤) : linearGrowthSup (fun _ => b) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `EReal.zero_ne_top`：zero_ne_top : (0 : EReal) != ⊤
· 使用定理 `EReal.zero_ne_bot`：zero_ne_bot : (0 : EReal) != ⊥
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
### Affine bounds
-/
lemma linearGrowthInf_le_of_eventually_le (hb : b ≠ ⊤) (h : ∀ᶠ n in atTop, u n ≤ v n + b) :
    linearGrowthInf u ≤ linearGrowthInf v := by
  apply (linearGrowthInf_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthInf_bot, bot_le]
  · apply (linearGrowthInf_add_le' _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthInf v)
    · exact Or.inr EReal.zero_ne_top
    · exact Or.inr EReal.zero_ne_bot
/-
**LinearGrowth.linearGrowthSup_le_of_eventually_le** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearGrowth`。
形式化陈述：linearGrowthSup_le_of_eventually_le (hb : b != ⊤) (h : forallᶠ n in atTop,
 u n <= v n + b) : linearGrowthSup u <= linearGrowthSup v
参数：hb : b != ⊤；h : forallᶠ n in atTop, u n <= v n + b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `LinearGrowth.linearGrowthSup_eventually_monotone`：linearGrowthSup_eventu
ally_monotone (h : u <=ᶠ[atTop] v) : linearGrowthSup u <= linearGrowthSup v
· 使用定理 `eq_bot_or_bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Order
Bot α] (a : α), a = ⊥ ∨ ⊥ < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EReal.add_bot`：add_bot (x : EReal) : x + ⊥ = ⊥
· 使用引理 `LinearGrowth.linearGrowthSup_bot`：linearGrowthSup_bot : linearGrowthSup 
(⊥ : Nat -> EReal) = (⊥ : EReal)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用引理 `LinearGrowth.linearGrowthSup_add_le`：linearGrowthSup_add_le (h : linearG
rowthSup u != ⊥ ∨ linearGrowthSup v != ⊤) (h' : linearGrowthSup u != ⊤ ∨ linearG
rowthSup v != ⊥) : linear…
· 使用引理 `LinearGrowth.linearGrowthSup_const`：linearGrowthSup_const (h : b != ⊥) (
h' : b != ⊤) : linearGrowthSup (fun _ => b) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `EReal.zero_ne_top`：zero_ne_top : (0 : EReal) != ⊤
· 使用定理 `EReal.zero_ne_bot`：zero_ne_bot : (0 : EReal) != ⊥
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma linearGrowthSup_le_of_eventually_le (hb : b ≠ ⊤) (h : ∀ᶠ n in atTop, u n ≤ v n + b) :
    linearGrowthSup u ≤ linearGrowthSup v := by
  apply (linearGrowthSup_eventually_monotone h).trans
  rcases eq_bot_or_bot_lt b with rfl | b_bot
  · simp only [add_bot, ← Pi.bot_def, linearGrowthSup_bot, bot_le]
  · apply (linearGrowthSup_add_le _ _).trans_eq <;> rw [linearGrowthSup_const b_bot.ne' hb]
    · exact add_zero (linearGrowthSup v)
    · exact Or.inr EReal.zero_ne_top
    · exact Or.inr EReal.zero_ne_bot

/-! ### Infimum and supremum -/

/-
**LinearGrowth.linearGrowthInf_inf** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_inf : linearGrowthInf (u ⊓ v) = min (linearGrowthInf u) (l
inearGrowthInf v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearGrowth.linearGrowthInf.eq_1`：∀ {R : Type u_1} [inst : Conditionall
yCompleteLattice R] [inst_1 : Div R] [inst_2 : NatCast R] (u : ℕ → R),   LinearG
rowth.linearGrowthInf u…
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
· 使用定理 `Monotone.map_min`：∀ {α : Type u} {β : Type v} [inst : LinearOrder α] [in
st_1 : LinearOrder β] {f : α → β} {a b : α},   Monotone f → f (min a b) = min (f
 a) (f…
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
lemma linearGrowthInf_inf :
    linearGrowthInf (u ⊓ v) = min (linearGrowthInf u) (linearGrowthInf v) := by
  rw [linearGrowthInf, linearGrowthInf, linearGrowthInf, ← liminf_min]
  refine liminf_congr (Eventually.of_forall fun n ↦ ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_min

/-- Lower linear growth as an `InfTopHom`. -/
/-
**LinearGrowth.linearGrowthInfTopHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInfTopHom : InfTopHom (Nat -> EReal) EReal where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LinearGrowth.linearGrowthInf_inf`：linearGrowthInf_inf : linearGrowthInf 
(u ⊓ v) = min (linearGrowthInf u) (linearGrowthInf v)
· 使用引理 `LinearGrowth.linearGrowthInf_top`：linearGrowthInf_top : linearGrowthInf 
⊤ = (⊤ : EReal)

--- 原说明 ---
Lower linear growth as an `InfTopHom`.
-/
noncomputable def linearGrowthInfTopHom : InfTopHom (ℕ → EReal) EReal where
  toFun := linearGrowthInf
  map_inf' _ _ := linearGrowthInf_inf
  map_top' := linearGrowthInf_top
/-
**LinearGrowth.linearGrowthInf_biInf** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_biInf {α : Type*} (u : α -> Nat -> EReal) {s : Set α} (hs 
: s.Finite) : linearGrowthInf (⨅ x in s, u x) = ⨅ x in s, linearGrowthInf (u x)
参数：u : α -> Nat -> EReal；hs : s.Finite。
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
· 使用引理 `LinearGrowth.linearGrowthInf_inf`：linearGrowthInf_inf : linearGrowthInf 
(u ⊓ v) = min (linearGrowthInf u) (linearGrowthInf v)
· 使用引理 `LinearGrowth.linearGrowthInf_top`：linearGrowthInf_top : linearGrowthInf 
⊤ = (⊤ : EReal)
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
lemma linearGrowthInf_biInf {α : Type*} (u : α → ℕ → EReal) {s : Set α} (hs : s.Finite) :
    linearGrowthInf (⨅ x ∈ s, u x) = ⨅ x ∈ s, linearGrowthInf (u x) := by
  have := map_finset_inf linearGrowthInfTopHom hs.toFinset u
  simpa only [linearGrowthInfTopHom, InfTopHom.coe_mk, InfHom.coe_mk, Finset.inf_eq_iInf,
    hs.mem_toFinset, comp_apply]
/-
**LinearGrowth.linearGrowthInf_iInf** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthInf_iInf {ι : Type*} [Finite ι] (u : ι -> Nat -> EReal) : line
arGrowthInf (⨅ i, u i) = ⨅ i, linearGrowthInf (u i)
参数：u : ι -> Nat -> EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iInf_univ`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {f
 : β → α}, ⨅ x ∈ Set.univ, f x = ⨅ x, f x
· 使用引理 `LinearGrowth.linearGrowthInf_biInf`：linearGrowthInf_biInf {α : Type*} (u
 : α -> Nat -> EReal) {s : Set α} (hs : s.Finite) : linearGrowthInf (⨅ x in s, u
 x) = ⨅ x in s, linearGr…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma linearGrowthInf_iInf {ι : Type*} [Finite ι] (u : ι → ℕ → EReal) :
    linearGrowthInf (⨅ i, u i) = ⨅ i, linearGrowthInf (u i) := by
  rw [← iInf_univ, linearGrowthInf_biInf u Set.finite_univ, iInf_univ]
/-
**LinearGrowth.linearGrowthSup_sup** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_sup : linearGrowthSup (u ⊔ v) = max (linearGrowthSup u) (l
inearGrowthSup v)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearGrowth.linearGrowthSup.eq_1`：∀ {R : Type u_1} [inst : Conditionall
yCompleteLattice R] [inst_1 : Div R] [inst_2 : NatCast R] (u : ℕ → R),   LinearG
rowth.linearGrowthSup u…
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
· 使用定理 `Monotone.map_max`：Monotone.map_max (hf : Monotone f) : f (max a b) = max
 (f a) (f b)
· 使用引理 `EReal.monotone_div_right_of_nonneg`：monotone_div_right_of_nonneg (h : 0 
<= b) : Monotone fun a => a / b
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
-/
lemma linearGrowthSup_sup :
    linearGrowthSup (u ⊔ v) = max (linearGrowthSup u) (linearGrowthSup v) := by
  rw [linearGrowthSup, linearGrowthSup, linearGrowthSup, ← limsup_max]
  refine limsup_congr (Eventually.of_forall fun n ↦ ?_)
  exact (monotone_div_right_of_nonneg n.cast_nonneg').map_max

/-- Upper linear growth as a `SupBotHom`. -/
/-
**LinearGrowth.linearGrowthSupBotHom** 是 Mathlib 中的一个定义，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSupBotHom : SupBotHom (Nat -> EReal) EReal where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `LinearGrowth.linearGrowthSup_sup`：linearGrowthSup_sup : linearGrowthSup 
(u ⊔ v) = max (linearGrowthSup u) (linearGrowthSup v)
· 使用引理 `LinearGrowth.linearGrowthSup_bot`：linearGrowthSup_bot : linearGrowthSup 
(⊥ : Nat -> EReal) = (⊥ : EReal)

--- 原说明 ---
Upper linear growth as a `SupBotHom`.
-/
noncomputable def linearGrowthSupBotHom : SupBotHom (ℕ → EReal) EReal where
  toFun := linearGrowthSup
  map_sup' _ _ := linearGrowthSup_sup
  map_bot' := linearGrowthSup_bot
/-
**LinearGrowth.linearGrowthSup_biSup** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_biSup {α : Type*} (u : α -> Nat -> EReal) {s : Set α} (hs 
: s.Finite) : linearGrowthSup (⨆ x in s, u x) = ⨆ x in s, linearGrowthSup (u x)
参数：u : α -> Nat -> EReal；hs : s.Finite。
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
· 使用引理 `LinearGrowth.linearGrowthSup_sup`：linearGrowthSup_sup : linearGrowthSup 
(u ⊔ v) = max (linearGrowthSup u) (linearGrowthSup v)
· 使用引理 `LinearGrowth.linearGrowthSup_bot`：linearGrowthSup_bot : linearGrowthSup 
(⊥ : Nat -> EReal) = (⊥ : EReal)
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
lemma linearGrowthSup_biSup {α : Type*} (u : α → ℕ → EReal) {s : Set α} (hs : s.Finite) :
    linearGrowthSup (⨆ x ∈ s, u x) = ⨆ x ∈ s, linearGrowthSup (u x) := by
  have := map_finset_sup linearGrowthSupBotHom hs.toFinset u
  simpa only [linearGrowthSupBotHom, SupBotHom.coe_mk, SupHom.coe_mk, Finset.sup_eq_iSup,
    hs.mem_toFinset, comp_apply]
/-
**LinearGrowth.linearGrowthSup_iSup** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_iSup {ι : Type*} [Finite ι] (u : ι -> Nat -> EReal) : line
arGrowthSup (⨆ i, u i) = ⨆ i, linearGrowthSup (u i)
参数：u : ι -> Nat -> EReal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSup_univ`：iSup_univ {f : β -> α} : ⨆ x in (univ : Set β), f x = ⨆ x, f 
x
· 使用引理 `LinearGrowth.linearGrowthSup_biSup`：linearGrowthSup_biSup {α : Type*} (u
 : α -> Nat -> EReal) {s : Set α} (hs : s.Finite) : linearGrowthSup (⨆ x in s, u
 x) = ⨆ x in s, linearGr…
· 使用定理 `Set.finite_univ`：∀ {α : Type u} [Finite α], Set.univ.Finite
-/
lemma linearGrowthSup_iSup {ι : Type*} [Finite ι] (u : ι → ℕ → EReal) :
    linearGrowthSup (⨆ i, u i) = ⨆ i, linearGrowthSup (u i) := by
  rw [← iSup_univ, linearGrowthSup_biSup u Set.finite_univ, iSup_univ]

end basic_properties

/-! ### Composition -/

section composition

variable {u : ℕ → EReal} {v : ℕ → ℕ}

/-
**LinearGrowth.Real.eventually_atTop_exists_int_between** 是 Mathlib 中的一个定理，位于命名空
间 `LinearGrowth.Real`。
形式化陈述：∀ {a b : ℝ}, a < b → ∀ᶠ (x : ℝ) in Filter.atTop, ∃ n, a * x ≤ ↑n ∧ ↑n ≤ b 
* x
参数：x : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `le_of_add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] 
[AddRightReflectLE α] {a b c : α}, b + a ≤ c + a → b ≤ c
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_sub_iff_add_le'`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : LE 
α] [AddLeftMono α] {a b c : α}, b ≤ c - a ↔ a + b ≤ c
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `inv_le_iff_one_le_mul₀`：inv_le_iff_one_le_mul₀ (ha : 0 < a) : a⁻¹ <= b ↔
 1 <= b * a
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `sub_pos_of_lt`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, b < a → 0 < a - b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋ + 1
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
-/
lemma Real.eventually_atTop_exists_int_between {a b : ℝ} (h : a < b) :
    ∀ᶠ x : ℝ in atTop, ∃ n : ℤ, a * x ≤ n ∧ n ≤ b * x := by
  refine (eventually_ge_atTop (b - a)⁻¹).mono fun x ab_x ↦ ?_
  rw [inv_le_iff_one_le_mul₀ (sub_pos_of_lt h), mul_comm, sub_mul, le_sub_iff_add_le'] at ab_x
  exact ⟨_, le_of_add_le_add_right (ab_x.trans (Int.lt_floor_add_one _).le), Int.floor_le _⟩
/-
**LinearGrowth.Real.eventually_atTop_exists_nat_between** 是 Mathlib 中的一个定理，位于命名空
间 `LinearGrowth.Real`。
形式化陈述：∀ {a b : ℝ}, a < b → 0 ≤ b → ∀ᶠ (x : ℝ) in Filter.atTop, ∃ n, a * x ≤ ↑n ∧
 ↑n ≤ b * x
参数：x : ℝ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `LinearGrowth.Real.eventually_atTop_exists_int_between`：∀ {a b : ℝ}, a < 
b → ∀ᶠ (x : ℝ) in Filter.atTop, ∃ n, a * x ≤ ↑n ∧ ↑n ≤ b * x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.cast_le`：∀ {R : Type u_1} [inst : AddCommGroupWithOne R] [inst_1 : P
artialOrder R] [AddLeftMono R] [ZeroLEOneClass R] [NeZero 1]   {m n : ℤ}, ↑m ≤ ↑
n…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Int.self_le_toNat`：∀ (a : ℤ), a ≤ ↑a.toNat
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Int.toNat_eq_max`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
lemma Real.eventually_atTop_exists_nat_between {a b : ℝ} (h : a < b) (hb : 0 ≤ b) :
    ∀ᶠ x : ℝ in atTop, ∃ n : ℕ, a * x ≤ n ∧ n ≤ b * x := by
  filter_upwards [eventually_ge_atTop 0, Real.eventually_atTop_exists_int_between h]
    with x x_0 ⟨m, m_a, m_b⟩
  refine ⟨m.toNat, m_a.trans (Int.cast_le.2 m.self_le_toNat), ?_⟩
  apply le_of_eq_of_le _ (max_le m_b (mul_nonneg hb x_0))
  exact_mod_cast Int.toNat_eq_max m
/-
**LinearGrowth.EReal.eventually_atTop_exists_nat_between** 是 Mathlib 中的一个定理，位于命名
空间 `LinearGrowth.EReal`。
形式化陈述：∀ {a b : EReal}, a < b → 0 ≤ b → ∀ᶠ (n : ℕ) in Filter.atTop, ∃ m, a * ↑n ≤
 ↑m ∧ ↑m ≤ b * ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_top_lt`：not_top_lt : ¬⊤ < a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `EReal.mul_nonpos_iff`：mul_nonpos_iff {a b : EReal} : a * b <= 0 ↔ 0 <= a
 ∧ b <= 0 ∨ a <= 0 ∧ 0 <= b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `EReal.instPosMulMono`：PosMulMono EReal
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用引理 `EReal.exists_nat_ge_mul`：exists_nat_ge_mul {a : EReal} (ha : a != ⊤) (n 
: Nat) : exists m : Nat, a * n <= m
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `EReal.top_mul_of_pos`：top_mul_of_pos {x : EReal} (h : 0 < x) : ⊤ * x = ⊤
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LinearGrowth.Real.eventually_atTop_exists_nat_between`：∀ {a b : ℝ}, a < 
b → 0 ≤ b → ∀ᶠ (x : ℝ) in Filter.atTop, ∃ n, a * x ≤ ↑n ∧ ↑n ≤ b * x
（共 40 条，此处仅展示前 30 条）
-/
lemma EReal.eventually_atTop_exists_nat_between {a b : EReal} (h : a < b) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∃ m : ℕ, a * n ≤ m ∧ m ≤ b * n :=
  match a with
  | ⊤ => (not_top_lt h).rec
  | ⊥ => by
    refine Eventually.of_forall fun n ↦ ⟨0, ?_, ?_⟩ <;> rw [Nat.cast_zero]
    · apply mul_nonpos_iff.2 -- Split apply and exact for a 0.5s. gain
      exact .inr ⟨bot_le, n.cast_nonneg'⟩
    · positivity
  | (a : ℝ) =>
    match b with
    | ⊤ => by
      refine (eventually_gt_atTop 0).mono fun n n_0 ↦ ?_
      obtain ⟨m, hm⟩ := exists_nat_ge_mul h.ne n
      exact ⟨m, hm, le_of_le_of_eq le_top (top_mul_of_pos (Nat.cast_pos'.2 n_0)).symm⟩
    | ⊥ => (not_lt_bot h).rec
    | (b : ℝ) => by
      obtain ⟨x, hx⟩ := eventually_atTop.1 <| Real.eventually_atTop_exists_nat_between
        (EReal.coe_lt_coe_iff.1 h) (EReal.coe_nonneg.1 hb)
      obtain ⟨n, x_n⟩ := exists_nat_ge x
      refine eventually_atTop.2 ⟨n, fun k n_k ↦ ?_⟩
      simp only [← coe_coe_eq_natCast, ← EReal.coe_mul, EReal.coe_le_coe_iff]
      exact hx k (x_n.trans (Nat.cast_le.2 n_k))
/-
**LinearGrowth.tendsto_atTop_of_linearGrowthInf_natCast_pos** 是 Mathlib 中的一个引理，位
于命名空间 `LinearGrowth`。
形式化陈述：tendsto_atTop_of_linearGrowthInf_natCast_pos (h : (linearGrowthInf fun n =
> v n : EReal) != 0) : Tendsto v atTop atTop
参数：h : (linearGrowthInf fun n => v n : EReal) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_atTop`：tendsto_atTop [Preorder β] {m : α -> β} {f : Filte
r α} : Tendsto m f atTop ↔ forall b, forallᶠ a in f, b <= m a
· 使用引理 `LinearGrowth.tendsto_atTop_of_linearGrowthInf_pos`：tendsto_atTop_of_line
arGrowthInf_pos (h : 0 < linearGrowthInf u) : Tendsto u atTop (𝓝 ⊤)
· 使用定理 `Ne.lt_of_le'`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≠ b 
→ b ≤ a → b < a
· 使用引理 `LinearGrowth.linearGrowthInf_natCast_nonneg`：linearGrowthInf_natCast_non
neg (v : Nat -> Nat) : 0 <= linearGrowthInf fun n => (v n : EReal)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EReal.tendsto_nhds_top_iff_real`：tendsto_nhds_top_iff_real {α : Type*} {
m : α -> EReal} {f : Filter α} : Tendsto m f (𝓝 ⊤) ↔ forall x : Real, forallᶠ a 
in f, ↑x < m a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma tendsto_atTop_of_linearGrowthInf_natCast_pos (h : (linearGrowthInf fun n ↦ v n : EReal) ≠ 0) :
    Tendsto v atTop atTop := by
  refine tendsto_atTop.2 fun M ↦ ?_
  have := tendsto_atTop_of_linearGrowthInf_pos (h.lt_of_le' (linearGrowthInf_natCast_nonneg v))
  exact (tendsto_nhds_top_iff_real.1 this M).mono fun n ↦ by exact_mod_cast le_of_lt
/-
**LinearGrowth.le_linearGrowthInf_comp** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：le_linearGrowthInf_comp (hu : 0 <=ᶠ[atTop] u) (hv : Tendsto v atTop atTop)
 : (linearGrowthInf fun n => v n : EReal) * linearGrowthInf u <= linearGrowthInf
 (u ∘ v)
参数：hu : 0 <=ᶠ[atTop] u；hv : Tendsto v atTop atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearGrowth.linearGrowthInf_const`：linearGrowthInf_const (h : b != ⊥) (
h' : b != ⊤) : linearGrowthInf (fun _ => b) = 0
· 使用定理 `EReal.zero_ne_bot`：zero_ne_bot : (0 : EReal) != ⊥
· 使用定理 `EReal.zero_ne_top`：zero_ne_top : (0 : EReal) != ⊤
· 使用引理 `LinearGrowth.linearGrowthInf_eventually_monotone`：linearGrowthInf_eventu
ally_monotone (h : u <=ᶠ[atTop] v) : linearGrowthInf u <= linearGrowthInf v
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用引理 `EReal.mul_le_of_forall_lt_of_nonneg`：mul_le_of_forall_lt_of_nonneg (ha :
 0 <= a) (hc : 0 <= c) (h : forall a' in Ioo 0 a, forall b' in Ioo 0 b, a' * b' 
<= c) : a * b <= c
· 使用引理 `LinearGrowth.linearGrowthInf_natCast_nonneg`：linearGrowthInf_natCast_non
neg (v : Nat -> Nat) : 0 <= linearGrowthInf fun n => (v n : EReal)
· 使用定理 `Eventually.le_linearGrowthInf`：∀ {u : ℕ → EReal} {a : EReal}, (∀ᶠ (n : ℕ
) in Filter.atTop, a * ↑n ≤ u n) → a ≤ LinearGrowth.linearGrowthInf u
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用引理 `LinearGrowth.eventually_mul_le`：eventually_mul_le (h : a < linearGrowthI
nf u) : forallᶠ n : Nat in atTop, a * n <= u n
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `EReal.lt_div_iff`：lt_div_iff (h : 0 < b) (h' : b != ⊤) : a < c / b ↔ a *
 b < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `instIsOrderedAddMonoidEReal`：IsOrderedAddMonoid EReal
· 使用定理 `instZeroLEOneClassEReal`：ZeroLEOneClass EReal
· 使用定理 `instCharZeroEReal`：CharZero EReal
· 使用定理 `EReal.natCast_ne_top`：natCast_ne_top (n : Nat) : (n : EReal) != ⊤
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
（共 36 条，此处仅展示前 30 条）
-/
lemma le_linearGrowthInf_comp (hu : 0 ≤ᶠ[atTop] u) (hv : Tendsto v atTop atTop) :
    (linearGrowthInf fun n ↦ v n : EReal) * linearGrowthInf u ≤ linearGrowthInf (u ∘ v) := by
  have uv_0 : 0 ≤ linearGrowthInf (u ∘ v) := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact linearGrowthInf_eventually_monotone (hv.eventually hu)
  apply EReal.mul_le_of_forall_lt_of_nonneg (linearGrowthInf_natCast_nonneg v) uv_0
  refine fun a ⟨_, a_v⟩ b ⟨b_0, b_u⟩ ↦ Eventually.le_linearGrowthInf ?_
  have b_uv := eventually_map.1 ((eventually_mul_le b_u).filter_mono hv)
  filter_upwards [b_uv, eventually_lt_of_lt_liminf a_v, eventually_gt_atTop 0]
    with n b_uvn a_vn n_0
  replace a_vn := ((lt_div_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 a_vn).le
  rw [comp_apply, mul_comm a b, mul_assoc b a]
  exact b_uvn.trans' <| by gcongr
/-
**LinearGrowth.linearGrowthSup_comp_le** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrowth`。
形式化陈述：linearGrowthSup_comp_le (hu : existsᶠ n in atTop, 0 <= u n) (hv₀ : (linear
GrowthSup fun n => v n : EReal) != 0) (hv₁ : (linearGrowthSup fun n => v n : ERe
al) != ⊤) (hv₂ : Tendsto v atTop atTop) : linearGrowthSup (u ∘ v) <= (linearGrow
thSup fun n => v n : EReal) * linearGrowthSup u
参数：hu : existsᶠ n in atTop, 0 <= u n；hv₀ : (linearGrowthSup fun n => v n : EReal
) != 0；hv₁ : (linearGrowthSup fun n => v n : EReal) != ⊤；hv₂ : Tendsto v atTop a
tTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `LinearGrowth.linearGrowthInf_natCast_nonneg`：linearGrowthInf_natCast_non
neg (v : Nat -> Nat) : 0 <= linearGrowthInf fun n => (v n : EReal)
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
· 使用引理 `EReal.le_mul_of_forall_lt`：le_mul_of_forall_lt (h₁ : 0 < a ∨ b != ⊤) (h₂
 : a != ⊤ ∨ 0 < b) (h : forall a' > a, forall b' > b, c <= a' * b') : c <= a * b
· 使用定理 `Eventually.linearGrowthSup_le`：∀ {u : ℕ → EReal} {a : EReal}, (∀ᶠ (n : ℕ
) in Filter.atTop, u n ≤ a * ↑n) → LinearGrowth.linearGrowthSup u ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearGrowth.linearGrowthInf_const`：linearGrowthInf_const (h : b != ⊥) (
h' : b != ⊤) : linearGrowthInf (fun _ => b) = 0
· 使用定理 `EReal.zero_ne_bot`：zero_ne_bot : (0 : EReal) != ⊥
· 使用定理 `EReal.zero_ne_top`：zero_ne_top : (0 : EReal) != ⊤
· 使用引理 `LinearGrowth.linearGrowthInf_le_linearGrowthSup_of_frequently_le`：linear
GrowthInf_le_linearGrowthSup_of_frequently_le (h : existsᶠ n in atTop, u n <= v 
n) : linearGrowthInf u <= linearGrowthSup v
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用引理 `LinearGrowth.eventually_le_mul`：eventually_le_mul (h : linearGrowthSup u
 < a) : forallᶠ n : Nat in atTop, u n <= a * n
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `EReal.div_lt_iff`：div_lt_iff (h : 0 < c) (h' : c != ⊤) : b / c < a ↔ b <
 a * c
（共 42 条，此处仅展示前 30 条）
-/
lemma linearGrowthSup_comp_le (hu : ∃ᶠ n in atTop, 0 ≤ u n)
    (hv₀ : (linearGrowthSup fun n ↦ v n : EReal) ≠ 0)
    (hv₁ : (linearGrowthSup fun n ↦ v n : EReal) ≠ ⊤) (hv₂ : Tendsto v atTop atTop) :
    linearGrowthSup (u ∘ v) ≤ (linearGrowthSup fun n ↦ v n : EReal) * linearGrowthSup u := by
  have v_0 := hv₀.symm.lt_of_le <| (linearGrowthInf_natCast_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) ?_
  refine fun a v_a b u_b ↦ Eventually.linearGrowthSup_le ?_
  have b_0 : 0 ≤ b := by
    rw [← linearGrowthInf_const zero_ne_bot zero_ne_top]
    exact (linearGrowthInf_le_linearGrowthSup_of_frequently_le hu).trans u_b.le
  have uv_b : ∀ᶠ n in atTop, u (v n) ≤ b * v n :=
    eventually_map.1 ((eventually_le_mul u_b).filter_mono hv₂)
  filter_upwards [uv_b, eventually_lt_of_limsup_lt v_a, eventually_gt_atTop 0]
    with n uvn_b vn_a n_0
  replace vn_a := ((div_lt_iff (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 vn_a).le
  rw [comp_apply, mul_comm a b, mul_assoc b a]
  exact uvn_b.trans <| by gcongr

/-! ### Monotone sequences -/

/-
**LinearGrowth._root_.Monotone.linearGrowthInf_nonneg** 是 Mathlib 中的一个引理，位于命名空间 
`LinearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Monotone sequences
-/
lemma _root_.Monotone.linearGrowthInf_nonneg (h : Monotone u) (h' : u ≠ ⊥) :
    0 ≤ linearGrowthInf u := by
  simp only [ne_eq, funext_iff, not_forall] at h'
  obtain ⟨m, hm⟩ := h'
  have m_n : ∀ᶠ n in atTop, u m ≤ u n := eventually_atTop.2 ⟨m, fun _ hb ↦ h hb⟩
  rcases eq_or_ne (u m) ⊤ with hm' | hm'
  · rw [hm'] at m_n
    exact le_top.trans (linearGrowthInf_top.symm.trans_le (linearGrowthInf_eventually_monotone m_n))
  · rw [← linearGrowthInf_const hm hm']
    exact linearGrowthInf_eventually_monotone m_n
/-
**LinearGrowth._root_.Monotone.linearGrowthSup_nonneg** 是 Mathlib 中的一个引理，位于命名空间 
`LinearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.linearGrowthSup_nonneg (h : Monotone u) (h' : u ≠ ⊥) :
    0 ≤ linearGrowthSup u :=
  (h.linearGrowthInf_nonneg h').trans (linearGrowthInf_le_linearGrowthSup)
/-
**LinearGrowth.linearGrowthInf_comp_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrow
th`。
形式化陈述：linearGrowthInf_comp_nonneg (h : Monotone u) (h' : u != ⊥) (hv : Tendsto v
 atTop atTop) : 0 <= linearGrowthInf (u ∘ v)
参数：h : Monotone u；h' : u != ⊥；hv : Tendsto v atTop atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用引理 `LinearGrowth.linearGrowthInf_eventually_monotone`：linearGrowthInf_eventu
ally_monotone (h : u <=ᶠ[atTop] v) : linearGrowthInf u <= linearGrowthInf v
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Pi.top_def`：∀ {ι : Type u_1} {α' : ι → Type u_2} [inst : (i : ι) → Top (
α' i)], ⊤ = fun x => ⊤
· 使用引理 `LinearGrowth.linearGrowthInf_top`：linearGrowthInf_top : linearGrowthInf 
⊤ = (⊤ : EReal)
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `LinearGrowth.linearGrowthInf_const`：linearGrowthInf_const (h : b != ⊥) (
h' : b != ⊤) : linearGrowthInf (fun _ => b) = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma linearGrowthInf_comp_nonneg (h : Monotone u) (h' : u ≠ ⊥) (hv : Tendsto v atTop atTop) :
    0 ≤ linearGrowthInf (u ∘ v) := by
  simp only [ne_eq, funext_iff, not_forall] at h'
  obtain ⟨m, hum⟩ := h'
  have um_uvn : ∀ᶠ n in atTop, u m ≤ (u ∘ v) n :=
    (eventually_atTop.2 ⟨m, fun n m_n ↦ h m_n⟩).filter_mono hv
  apply (linearGrowthInf_eventually_monotone um_uvn).trans'
  rcases eq_or_ne (u m) ⊤ with hum' | hum'
  · rw [hum', ← Pi.top_def, linearGrowthInf_top]; exact le_top
  · rw [linearGrowthInf_const hum hum']
/-
**LinearGrowth.linearGrowthSup_comp_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `LinearGrow
th`。
形式化陈述：linearGrowthSup_comp_nonneg (h : Monotone u) (h' : u != ⊥) (hv : Tendsto v
 atTop atTop) : 0 <= linearGrowthSup (u ∘ v)
参数：h : Monotone u；h' : u != ⊥；hv : Tendsto v atTop atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `LinearGrowth.linearGrowthInf_comp_nonneg`：linearGrowthInf_comp_nonneg (h
 : Monotone u) (h' : u != ⊥) (hv : Tendsto v atTop atTop) : 0 <= linearGrowthInf
 (u ∘ v)
· 使用引理 `LinearGrowth.linearGrowthInf_le_linearGrowthSup`：linearGrowthInf_le_line
arGrowthSup (h : IsBoundedUnder (· <= ·) atTop fun n => u n / n
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
-/
lemma linearGrowthSup_comp_nonneg (h : Monotone u) (h' : u ≠ ⊥) (hv : Tendsto v atTop atTop) :
    0 ≤ linearGrowthSup (u ∘ v) :=
  (linearGrowthInf_comp_nonneg h h' hv).trans linearGrowthInf_le_linearGrowthSup
/-
**LinearGrowth._root_.Monotone.linearGrowthInf_comp_le** 是 Mathlib 中的一个引理，位于命名空间
 `LinearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.linearGrowthInf_comp_le (h : Monotone u)
    (hv₀ : (linearGrowthSup fun n ↦ v n : EReal) ≠ 0)
    (hv₁ : (linearGrowthSup fun n ↦ v n : EReal) ≠ ⊤) :
    linearGrowthInf (u ∘ v) ≤ (linearGrowthSup fun n ↦ v n : EReal) * linearGrowthInf u := by
  -- First we apply `le_mul_of_forall_lt`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthInf_bot]; exact bot_le
  have v_0 := hv₀.symm.lt_of_le <| (linearGrowthInf_natCast_nonneg v).trans (liminf_le_limsup)
  refine le_mul_of_forall_lt (.inl v_0) (.inl hv₁) fun a v_a b u_b ↦ ?_
  have a_0 := v_0.trans v_a
  have b_0 := (h.linearGrowthInf_nonneg u_0).trans_lt u_b
  rcases eq_or_ne a ⊤ with rfl | a_top
  · rw [top_mul_of_pos b_0]; exact le_top
  apply Frequently.linearGrowthInf_le
  obtain ⟨a', v_a', a_a'⟩ := exists_between v_a
  -- We get an epsilon of room: if `m` is large enough, then `v n ≤ a' * n < a * n`.
  -- Using `u_b`, we can find arbitrarily large values `n` such that `u n ≤ b * n`.
  -- If such an `n` is large enough, then we can find an integer `k` such that
  -- `a⁻¹ * n ≤ k ≤ a'⁻¹ * n`, or, in other words, `a' * k ≤ n ≤ a * k`.
  -- Then `v k ≤ a' * k ≤ n`, so `u (v k) ≤ u n ≤ b * n ≤ b * a * k`.
  have a_0' := v_0.trans v_a'
  have a_a_inv' : a⁻¹ < a'⁻¹ := inv_strictAntiOn (Set.mem_Ioi.2 a_0') (Set.mem_Ioi.2 a_0) a_a'
  replace v_a' : ∀ᶠ n : ℕ in atTop, v n ≤ a' * n := by
    filter_upwards [eventually_lt_of_limsup_lt v_a', eventually_gt_atTop 0] with n vn_a' n_0
    rw [mul_comm]
    exact (div_le_iff_le_mul (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 vn_a'.le
  suffices h : (∀ᶠ n : ℕ in atTop, v n ≤ a' * n) → ∃ᶠ n : ℕ in atTop, (u ∘ v) n ≤ a * b * n
    from h v_a'
  rw [← frequently_imp_distrib]
  replace u_b := ((frequently_le_mul u_b).and_eventually (eventually_gt_atTop 0)).and_eventually
    <| EReal.eventually_atTop_exists_nat_between a_a_inv' (inv_nonneg_of_nonneg a_0'.le)
  refine frequently_atTop.2 fun M ↦ ?_
  obtain ⟨M', aM_M'⟩ := exists_nat_ge_mul a_top M
  obtain ⟨n, n_M', ⟨un_bn, _⟩, k, an_k, k_an'⟩ := frequently_atTop.1 u_b M'
  refine ⟨k, ?_, fun vk_ak' ↦ ?_⟩
  · rw [mul_comm a, ← le_div_iff_mul_le a_0 a_top, EReal.div_eq_inv_mul] at aM_M'
    apply Nat.cast_le.1 <| aM_M'.trans <| an_k.trans' _
    gcongr
  · rw [comp_apply, mul_comm a b, mul_assoc b a]
    rw [← EReal.div_eq_inv_mul, le_div_iff_mul_le a_0' (ne_top_of_lt a_a'), mul_comm] at k_an'
    rw [← EReal.div_eq_inv_mul, div_le_iff_le_mul a_0 a_top] at an_k
    have vk_n := Nat.cast_le.1 (vk_ak'.trans k_an')
    exact (h vk_n).trans <| un_bn.trans <| by gcongr
/-
**LinearGrowth._root_.Monotone.le_linearGrowthSup_comp** 是 Mathlib 中的一个引理，位于命名空间
 `LinearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.le_linearGrowthSup_comp (h : Monotone u)
    (hv : (linearGrowthInf fun n ↦ v n : EReal) ≠ 0) :
    (linearGrowthInf fun n ↦ v n : EReal) * linearGrowthSup u ≤ linearGrowthSup (u ∘ v) := by
  have v_0 := hv.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  -- WLOG, `u` is non-bot, and we can apply `mul_le_of_forall_lt_of_nonneg`.
  by_cases u_0 : u = ⊥
  · rw [u_0, linearGrowthSup_bot, mul_bot_of_pos v_0]; exact bot_le
  apply EReal.mul_le_of_forall_lt_of_nonneg v_0.le
    (linearGrowthSup_comp_nonneg h u_0 (tendsto_atTop_of_linearGrowthInf_natCast_pos hv))
  intro a ⟨a_0, a_v⟩ b ⟨b_0, b_u⟩
  apply Frequently.le_linearGrowthSup
  obtain ⟨a', a_a', a_v'⟩ := exists_between a_v
  -- We get an epsilon of room: if `m` is large enough, then `a * n < a' * n ≤ v n`.
  -- Using `b_u`, we can find arbitrarily large values `n` such that `b * n ≤ u n`.
  -- If such an `n` is large enough, then we can find an integer `k` such that
  -- `a'⁻¹ * n ≤ k ≤ a⁻¹ * n`, or, in other words, `a * k ≤ n ≤ a' * k`.
  -- Then `v k ≥ a' * k ≥ n`, so `u (v k) ≥ u n ≥ b * n ≥ b * a * k`.
  have a_top' := ne_top_of_lt a_v'
  have a_0' := a_0.trans a_a'
  have a_a_inv' : a'⁻¹ < a⁻¹ := inv_strictAntiOn (Set.mem_Ioi.2 a_0) (Set.mem_Ioi.2 a_0') a_a'
  replace a_v' : ∀ᶠ n : ℕ in atTop, a' * n ≤ v n := by
    filter_upwards [eventually_lt_of_lt_liminf a_v', eventually_gt_atTop 0] with n a_vn' n_0
    exact (le_div_iff_mul_le (Nat.cast_pos'.2 n_0) (natCast_ne_top n)).1 a_vn'.le
  suffices h : (∀ᶠ n : ℕ in atTop, a' * n ≤ v n) → ∃ᶠ n : ℕ in atTop, a * b * n ≤ (u ∘ v) n
    from h a_v'
  rw [← frequently_imp_distrib]
  replace b_u := ((frequently_mul_le b_u).and_eventually (eventually_gt_atTop 0)).and_eventually
    <| EReal.eventually_atTop_exists_nat_between a_a_inv' (inv_nonneg_of_nonneg a_0.le)
  refine frequently_atTop.2 fun M ↦ ?_
  obtain ⟨M', aM_M'⟩ := exists_nat_ge_mul a_top' M
  obtain ⟨n, n_M', ⟨bn_un, _⟩, k, an_k', k_an⟩ := frequently_atTop.1 b_u M'
  refine ⟨k, ?_, fun ak_vk' ↦ ?_⟩
  · rw [mul_comm a', ← le_div_iff_mul_le a_0' a_top', EReal.div_eq_inv_mul] at aM_M'
    apply Nat.cast_le.1 <| aM_M'.trans <| an_k'.trans' _
    gcongr
  · rw [comp_apply, mul_comm a b, mul_assoc b a]
    rw [← EReal.div_eq_inv_mul, div_le_iff_le_mul a_0' a_top'] at an_k'
    rw [← EReal.div_eq_inv_mul, le_div_iff_mul_le a_0 (ne_top_of_lt a_a'), mul_comm] at k_an
    have n_vk := Nat.cast_le.1 (an_k'.trans ak_vk')
    exact le_trans (by gcongr) <| bn_un.trans (h n_vk)
/-
**LinearGrowth._root_.Monotone.linearGrowthInf_comp** 是 Mathlib 中的一个引理，位于命名空间 `L
inearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.linearGrowthInf_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (𝓝 a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    linearGrowthInf (u ∘ v) = a * linearGrowthInf u := by
  have hv₁ : 0 < liminf (fun n ↦ (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  have v_top := tendsto_atTop_of_linearGrowthInf_natCast_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` is eventually larger than one.
  -- In the latter case, we apply `le_linearGrowthInf_comp` and `linearGrowthInf_comp_le`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthInf_bot, ← hv.liminf_eq, mul_bot_of_pos hv₁]
  by_cases! h' : ∃ᶠ n : ℕ in atTop, u n ≤ 0
  · replace h' (n : ℕ) : u n ≤ 0 := by
      obtain ⟨m, n_m, um_1⟩ := (frequently_atTop.1 h') n
      exact (h n_m).trans um_1
    have u_0' : linearGrowthInf u = 0 := by
      apply le_antisymm _ (h.linearGrowthInf_nonneg u_0)
      exact (linearGrowthInf_monotone h').trans_eq (linearGrowthInf_const zero_ne_bot zero_ne_top)
    rw [u_0', mul_zero]
    apply le_antisymm _ (linearGrowthInf_comp_nonneg h u_0 v_top)
    apply (linearGrowthInf_monotone fun n ↦ h' (v n)).trans_eq
    exact linearGrowthInf_const zero_ne_bot zero_ne_top
  · replace h' := h'.mono fun _ hn ↦ hn.le
    apply le_antisymm
    · rw [← hv.limsup_eq] at ha ha' ⊢
      exact h.linearGrowthInf_comp_le ha ha'
    · rw [← hv.liminf_eq]
      exact le_linearGrowthInf_comp h' v_top
/-
**LinearGrowth._root_.Monotone.linearGrowthSup_comp** 是 Mathlib 中的一个引理，位于命名空间 `L
inearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.linearGrowthSup_comp {a : EReal} (h : Monotone u)
    (hv : Tendsto (fun n ↦ (v n : EReal) / n) atTop (𝓝 a)) (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    linearGrowthSup (u ∘ v) = a * linearGrowthSup u := by
  have hv₁ : 0 < liminf (fun n ↦ (v n : EReal) / n) atTop := by
    rw [← hv.liminf_eq] at ha
    exact ha.symm.lt_of_le (linearGrowthInf_natCast_nonneg v)
  have v_top := tendsto_atTop_of_linearGrowthInf_natCast_pos hv₁.ne.symm
  -- Either `u = 0`, or `u` is non-zero and bounded by `1`, or `u` is eventually larger than one.
  -- In the latter case, we apply `le_linearGrowthSup_comp` and `linearGrowthSup_comp_le`.
  by_cases u_0 : u = ⊥
  · rw [u_0, Pi.bot_comp, linearGrowthSup_bot, ← hv.liminf_eq, mul_bot_of_pos hv₁]
  by_cases! u_1 : ∀ᶠ n : ℕ in atTop, u n ≤ 0
  · have u_0' : linearGrowthSup u = 0 := by
      apply le_antisymm _ (h.linearGrowthSup_nonneg u_0)
      apply (linearGrowthSup_eventually_monotone u_1).trans_eq
      exact (linearGrowthSup_const zero_ne_bot zero_ne_top)
    rw [u_0', mul_zero]
    apply le_antisymm _ (linearGrowthSup_comp_nonneg h u_0 v_top)
    apply (linearGrowthSup_eventually_monotone (v_top.eventually u_1)).trans_eq
    exact linearGrowthSup_const zero_ne_bot zero_ne_top
  · replace u_1 := u_1.mono fun x hx ↦ hx.le
    apply le_antisymm
    · rw [← hv.limsup_eq] at ha ha' ⊢
      exact linearGrowthSup_comp_le u_1 ha ha' v_top
    · rw [← hv.liminf_eq]
      exact h.le_linearGrowthSup_comp hv₁.ne.symm
/-
**LinearGrowth._root_.Monotone.linearGrowthInf_comp_mul** 是 Mathlib 中的一个引理，位于命名空
间 `LinearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.linearGrowthInf_comp_mul {m : ℕ} (h : Monotone u) (hm : m ≠ 0) :
    linearGrowthInf (fun n ↦ u (m * n)) = m * linearGrowthInf u := by
  have : Tendsto (fun n : ℕ ↦ ((m * n : ℕ) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx ↦ ?_)
    rw [mul_comm, natCast_mul x m, ← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_ne_zero.2 hx.ne.symm)
  exact h.linearGrowthInf_comp this (Nat.cast_ne_zero.2 hm) (natCast_ne_top m)
/-
**LinearGrowth._root_.Monotone.linearGrowthSup_comp_mul** 是 Mathlib 中的一个引理，位于命名空
间 `LinearGrowth`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Monotone.linearGrowthSup_comp_mul {m : ℕ} (h : Monotone u) (hm : m ≠ 0) :
    linearGrowthSup (fun n ↦ u (m * n)) = m * linearGrowthSup u := by
  have : Tendsto (fun n : ℕ ↦ ((m * n : ℕ) : EReal) / n) atTop (𝓝 m) := by
    refine tendsto_nhds_of_eventually_eq ((eventually_gt_atTop 0).mono fun x hx ↦ ?_)
    rw [mul_comm, natCast_mul x m, ← mul_div]
    exact mul_div_cancel (natCast_ne_bot x) (natCast_ne_top x) (Nat.cast_ne_zero.2 hx.ne.symm)
  exact h.linearGrowthSup_comp this (Nat.cast_ne_zero.2 hm) (natCast_ne_top m)

end composition

end LinearGrowth

