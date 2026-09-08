/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# Summability of logarithms

We give conditions under which the logarithms of a summable sequence are summable. We also use this
to relate summability of `f` to multipliability of `1 + f`.

-/

public section

variable {ι : Type*}

open Filter Topology NNReal SummationFilter

namespace Complex
variable {f : ι → ℂ} {a : ℂ}

/-
**Complex.hasProd_of_hasSum_log** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：hasProd_of_hasSum_log (hfn : forall i, f i != 0) (hf : HasSum (fun i => lo
g (f i)) a) : HasProd f (exp a)
参数：hfn : forall i, f i != 0；hf : HasSum (fun i => log (f i)) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Complex.exp_log`：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `HasSum.cexp`：HasSum.cexp {ι : Type*} {f : ι -> Complex} {a : Complex} (h
 : HasSum f a) : HasProd (cexp ∘ f) (cexp a)
-/
lemma hasProd_of_hasSum_log (hfn : ∀ i, f i ≠ 0) (hf : HasSum (fun i ↦ log (f i)) a) :
    HasProd f (exp a) :=
  hf.cexp.congr (by simp [exp_log, hfn])
/-
**Complex.multipliable_of_summable_log** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：multipliable_of_summable_log (hf : Summable fun i => log (f i)) : Multipli
able f
参数：hf : Summable fun i => log (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `multipliable_of_exists_eq_zero`：multipliable_of_exists_eq_zero (hf : exi
sts b, f b = 0) [L.LeAtTop] : Multipliable f L
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用引理 `Complex.hasProd_of_hasSum_log`：hasProd_of_hasSum_log (hfn : forall i, f 
i != 0) (hf : HasSum (fun i => log (f i)) a) : HasProd f (exp a)
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
lemma multipliable_of_summable_log (hf : Summable fun i ↦ log (f i)) :
    Multipliable f := by
  by_cases! hfn : ∃ n, f n = 0
  · exact multipliable_of_exists_eq_zero hfn
  · exact ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

/-- The exponential of a convergent sum of complex logs is the corresponding infinite product. -/
/-
**Complex.cexp_tsum_eq_tprod** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：cexp_tsum_eq_tprod (hfn : forall i, f i != 0) (hf : Summable fun i => log 
(f i)) : cexp (∑' i, log (f i)) = ∏' i, f i
参数：hfn : forall i, f i != 0；hf : Summable fun i => log (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `Complex.hasProd_of_hasSum_log`：hasProd_of_hasSum_log (hfn : forall i, f 
i != 0) (hf : HasSum (fun i => log (f i)) a) : HasProd f (exp a)
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…

--- 原说明 ---
The exponential of a convergent sum of complex logs is the corresponding infinit
e product.
-/
lemma cexp_tsum_eq_tprod (hfn : ∀ i, f i ≠ 0) (hf : Summable fun i ↦ log (f i)) :
    cexp (∑' i, log (f i)) = ∏' i, f i :=
  (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm
/-
**Complex.summable_log_one_add_of_summable** 是 Mathlib 中的一个引理，位于命名空间 `Complex`。
形式化陈述：summable_log_one_add_of_summable {f : ι -> Complex} (hf : Summable f) : Su
mmable (fun i => log (1 + f i))
参数：hf : Summable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm_bounded_eventually`：Summable.of_norm_bounded_eventually
 {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i in cofinite, ‖f i
‖ <= g i) : Summable f
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Summable.norm`：∀ {α : Type u_1} {E : Type u_2} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]   {f : α → E}, Summable 
f →…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_le_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Summable.tendsto_cofinite_zero`：∀ {α : Type u_1} {G : Type u_4} [inst : 
TopologicalSpace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   {f : α
 → G}, Summable f → …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Complex.norm_log_one_add_half_le_self`：norm_log_one_add_half_le_self {z 
: Complex} (hz : ‖z‖ <= 1 / 2) : ‖log (1 + z)‖ <= (3 / 2) * ‖z‖
-/
lemma summable_log_one_add_of_summable {f : ι → ℂ} (hf : Summable f) :
    Summable (fun i ↦ log (1 + f i)) := by
  apply (hf.norm.mul_left (3 / 2)).of_norm_bounded_eventually
  filter_upwards [hf.norm.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi
    using norm_log_one_add_half_le_self hi
/-
**Complex.multipliable_one_add_of_summable** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {ι : Type u_1} {f : ι → ℂ}, Summable f → Multipliable fun i => 1 + f i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.multipliable_of_summable_log`：multipliable_of_summable_log (hf :
 Summable fun i => log (f i)) : Multipliable f
· 使用引理 `Complex.summable_log_one_add_of_summable`：summable_log_one_add_of_summab
le {f : ι -> Complex} (hf : Summable f) : Summable (fun i => log (1 + f i))
-/
protected lemma multipliable_one_add_of_summable (hf : Summable f) :
    Multipliable (fun i ↦ 1 + f i) :=
  multipliable_of_summable_log (summable_log_one_add_of_summable hf)

end Complex

namespace Real
variable {f : ι → ℝ} {a : ℝ}

/-
**Real.hasProd_of_hasSum_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：hasProd_of_hasSum_log (hfn : forall i, 0 < f i) (hf : HasSum (fun i => log
 (f i)) a) : HasProd f (rexp a)
参数：hfn : forall i, 0 < f i；hf : HasSum (fun i => log (f i)) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `HasSum.rexp`：HasSum.rexp {ι} {f : ι -> Real} {a : Real} (h : HasSum f a)
 : HasProd (rexp ∘ f) (rexp a)
-/
lemma hasProd_of_hasSum_log (hfn : ∀ i, 0 < f i) (hf : HasSum (fun i ↦ log (f i)) a) :
    HasProd f (rexp a) :=
  hf.rexp.congr (by simp [exp_log, hfn])
/-
**Real.multipliable_of_summable_log** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：multipliable_of_summable_log (hfn : forall i, 0 < f i) (hf : Summable fun 
i => log (f i)) : Multipliable f
参数：hfn : forall i, 0 < f i；hf : Summable fun i => log (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.hasProd_of_hasSum_log`：hasProd_of_hasSum_log (hfn : forall i, 0 < f
 i) (hf : HasSum (fun i => log (f i)) a) : HasProd f (rexp a)
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
-/
lemma multipliable_of_summable_log (hfn : ∀ i, 0 < f i) (hf : Summable fun i ↦ log (f i)) :
    Multipliable f :=
  ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

/-- Alternate version of `Real.multipliable_of_summable_log` assuming only that positivity holds
eventually. -/
/-
**Real.multipliable_of_summable_log'** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：multipliable_of_summable_log' (hfn : forallᶠ i in cofinite, 0 < f i) (hf :
 Summable fun i => log (f i)) : Multipliable f
参数：hfn : forallᶠ i in cofinite, 0 < f i；hf : Summable fun i => log (f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.congr_cofinite`：∀ {α : Type u_1} {β : Type u_2} [inst : AddComm
Group α] [inst_1 : TopologicalSpace α] [IsTopologicalAddGroup α]   {f g : β → α}
, Summable f …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Real.multipliable_of_summable_log`：multipliable_of_summable_log (hfn : f
orall i, 0 < f i) (hf : Summable fun i => log (f i)) : Multipliable f
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Multipliable.congr_cofinite₀`：Multipliable.congr_cofinite₀ (hf : Multipl
iable f) (hf' : forall a, f a != 0) (hfg : forallᶠ a in cofinite, f a = g a) : M
ultipliable g
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Alternate version of `Real.multipliable_of_summable_log` assuming only that posi
tivity holds
eventually.
-/
lemma multipliable_of_summable_log' (hfn : ∀ᶠ i in cofinite, 0 < f i)
    (hf : Summable fun i ↦ log (f i)) : Multipliable f := by
  have : Summable fun i ↦ log (if 0 < f i then f i else 1) := by
    apply hf.congr_cofinite
    filter_upwards [hfn] with i hi using by simp [hi]
  have : Multipliable fun i ↦ if 0 < f i then f i else 1 := by
    refine multipliable_of_summable_log (fun i ↦ ?_) this
    split_ifs with h <;> simp [h]
  refine this.congr_cofinite₀ (fun i ↦ ?_) ?_
  · split_ifs with h <;> simp [h, ne_of_gt]
  · filter_upwards [hfn] with i hi using by simp [hi]

/-- The exponential of a convergent sum of real logs is the corresponding infinite product. -/
/-
**Real.rexp_tsum_eq_tprod** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：rexp_tsum_eq_tprod (hfn : forall i, 0 < f i) (hf : Summable fun i => log (
f i)) : rexp (∑' i, log (f i)) = ∏' i, f i
参数：hfn : forall i, 0 < f i；hf : Summable fun i => log (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasProd.tprod_eq`：HasProd.tprod_eq (ha : HasProd f a L) : ∏'[L] b, f b =
 a
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `Real.hasProd_of_hasSum_log`：hasProd_of_hasSum_log (hfn : forall i, 0 < f
 i) (hf : HasSum (fun i => log (f i)) a) : HasProd f (rexp a)
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…

--- 原说明 ---
The exponential of a convergent sum of real logs is the corresponding infinite p
roduct.
-/
lemma rexp_tsum_eq_tprod (hfn : ∀ i, 0 < f i) (hf : Summable fun i ↦ log (f i)) :
    rexp (∑' i, log (f i)) = ∏' i, f i :=
  (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm

open Complex in
/-
**Real.summable_log_one_add_of_summable** 是 Mathlib 中的一个引理，位于命名空间 `Real`。
形式化陈述：summable_log_one_add_of_summable (hf : Summable f) : Summable (fun i => lo
g (1 + f i))
参数：hf : Summable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.summable_ofReal`：∀ {α : Type u_1} {L : SummationFilter α} {f : α
 → ℝ}, Summable (fun x => ↑(f x)) L ↔ Summable f L
· 使用定理 `Summable.congr_cofinite`：∀ {α : Type u_1} {β : Type u_2} [inst : AddComm
Group α] [inst_1 : TopologicalSpace α] [IsTopologicalAddGroup α]   {f g : β → α}
, Summable f …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用引理 `Complex.summable_log_one_add_of_summable`：summable_log_one_add_of_summab
le {f : ι -> Complex} (hf : Summable f) : Summable (fun i => log (1 + f i))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_const_le`：Filter.Tendsto.eventually_const_le {
l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v) (h : Tendsto f l (𝓝 v)) : fora
llᶠ a in l, u <= f a
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `neg_one_lt_zero`：neg_one_lt_zero [ZeroLEOneClass R] [NeZero (1 : R)] [Ad
dLeftStrictMono R] : -1 < (0 : R)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Summable.tendsto_cofinite_zero`：∀ {α : Type u_1} {G : Type u_4} [inst : 
TopologicalSpace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   {f : α
 → G}, Summable f → …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Complex.ofReal_log`：ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Compl
ex) = log x
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 55 条，此处仅展示前 30 条）
-/
lemma summable_log_one_add_of_summable (hf : Summable f) :
    Summable (fun i ↦ log (1 + f i)) := by
  rw [← summable_ofReal]
  apply (Complex.summable_log_one_add_of_summable (summable_ofReal.mpr hf)).congr_cofinite
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_le neg_one_lt_zero] with i hi
  rw [ofReal_log, ofReal_add, ofReal_one]
  linarith
/-
**Real.multipliable_one_add_of_summable** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：∀ {ι : Type u_1} {f : ι → ℝ}, Summable f → Multipliable fun i => 1 + f i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Real.multipliable_of_summable_log'`：multipliable_of_summable_log' (hfn :
 forallᶠ i in cofinite, 0 < f i) (hf : Summable fun i => log (f i)) : Multipliab
le f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_const_lt`：Filter.Tendsto.eventually_const_lt {
l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v) (h : Filter.Tendsto f l (𝓝 v))
 : forallᶠ a in l, u < f…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `neg_one_lt_zero`：neg_one_lt_zero [ZeroLEOneClass R] [NeZero (1 : R)] [Ad
dLeftStrictMono R] : -1 < (0 : R)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Summable.tendsto_cofinite_zero`：∀ {α : Type u_1} {G : Type u_4} [inst : 
TopologicalSpace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   {f : α
 → G}, Summable f → …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 49 条，此处仅展示前 30 条）
-/
protected lemma multipliable_one_add_of_summable (hf : Summable f) :
    Multipliable (fun i ↦ 1 + f i) := by
  refine multipliable_of_summable_log' ?_ (summable_log_one_add_of_summable hf)
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_lt neg_one_lt_zero] with i hi
  linarith

end Real

/-
**summable_finsetProd_of_summable_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_finsetProd_of_summable_nonneg {f : ι -> Real} (hf : forall i, 0 <
= f i) (hfs : Summable f) : Summable (fun s : Finset ι => ∏ i in s, f i)
参数：hf : forall i, 0 <= f i；hfs : Summable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_sum_le`：summable_of_sum_le {ι : Type*} {f : ι -> Real} {c : 
Real} (hf : 0 <= f) (h : forall u : Finset ι, ∑ x in u, f x <= c) : Summable f
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `Finset.sum_le_sum_of_subset_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [
inst : AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} {s t : Finset ι}   [Ad
dLeftMono N], s ⊆ t → (∀ i …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t
· 使用引理 `Finset.subset_biUnion_of_mem`：subset_biUnion_of_mem (u : α -> Finset β) 
{x : α} (xs : x in s) : u x subseteq s.biUnion u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_one_add`：prod_one_add {f : ι -> R} (s : Finset ι) : ∏ i in s
, (1 + f i) = ∑ t in s.powerset, ∏ i in t, f i
· 使用定理 `Real.prod_one_add_le_exp_sum`：prod_one_add_le_exp_sum {ι : Type*} (s : F
inset ι) {f : ι -> Real} (hf : forall i, 0 <= f i) : ∏ i in s, (1 + f i) <= exp 
(∑ i in s, f i)
· 使用定理 `Real.exp_le_exp`：exp_le_exp {x y : Real} : exp x <= exp y ↔ x <= y
· 使用定理 `Summable.sum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFilt
er ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [i
nst_3 : To…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
lemma summable_finsetProd_of_summable_nonneg {f : ι → ℝ} (hf : ∀ i, 0 ≤ f i)
    (hfs : Summable f) : Summable (fun s : Finset ι ↦ ∏ i ∈ s, f i) := by
  classical
  refine summable_of_sum_le (c := Real.exp (∑' i, f i))
    (fun s ↦ Finset.prod_nonneg fun i _ ↦ hf i) fun T ↦ ?_
  calc ∑ s ∈ T, ∏ i ∈ s, f i
      ≤ ∑ s ∈ (T.biUnion id).powerset, ∏ i ∈ s, f i :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun s hs ↦ Finset.mem_powerset.mpr
          (Finset.subset_biUnion_of_mem id hs)) (fun s _ _ ↦ Finset.prod_nonneg fun i _ ↦ hf i)
    _ = ∏ i ∈ T.biUnion id, (1 + f i) := (Finset.prod_one_add _).symm
    _ ≤ Real.exp (∑ i ∈ T.biUnion id, f i) := Real.prod_one_add_le_exp_sum _ hf
    _ ≤ Real.exp (∑' i, f i) :=
        Real.exp_le_exp.mpr (hfs.sum_le_tsum _ fun _ _ ↦ hf _)

@[deprecated (since := "2026-04-08")]
alias summable_finset_prod_of_summable_nonneg := summable_finsetProd_of_summable_nonneg

section NormedRing

/-
**Multipliable.eventually_bounded_finsetProd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Multipliable.eventually_bounded_finsetProd {v : ι -> Real} (hv : Multiplia
ble v) : exists r₁ > 0, exists s₁, forall t, s₁ subseteq t -> ∏ i in t, v i <= r
₁
参数：hv : Multipliable v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.Tendsto.eventually_le_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_lt_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max b c <
 a ↔ b < a ∧ c < a
· 使用定理 `Multipliable.hasProd`：Multipliable.hasProd (ha : Multipliable f L) : Has
Prod f (∏'[L] b, f b) L
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SummationFilter.unconditional.eq_1`：∀ (β : Type u_2), SummationFilter.un
conditional β = { filter := Filter.atTop }
-/
lemma Multipliable.eventually_bounded_finsetProd {v : ι → ℝ} (hv : Multipliable v) :
    ∃ r₁ > 0, ∃ s₁, ∀ t, s₁ ⊆ t → ∏ i ∈ t, v i ≤ r₁ := by
  obtain ⟨r₁, hr₁⟩ := exists_gt (max 0 <| ∏' i, v i)
  rw [max_lt_iff] at hr₁
  have := hv.hasProd.eventually_le_const hr₁.2
  rw [unconditional, eventually_atTop] at this
  exact ⟨r₁, hr₁.1, this⟩

@[deprecated (since := "2026-04-08")]
alias Multipliable.eventually_bounded_finset_prod := Multipliable.eventually_bounded_finsetProd

variable {R : Type*} [NormedCommRing R] [NormOneClass R] {f : ι → R}
/-
**multipliable_norm_one_add_of_summable_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multipliable_norm_one_add_of_summable_norm (hf : Summable fun i => ‖f i‖) 
: Multipliable fun i => ‖1 + f i‖
参数：hf : Summable fun i => ‖f i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Real.multipliable_one_add_of_summable`：∀ {ι : Type u_1} {f : ι → ℝ}, Sum
mable f → Multipliable fun i => 1 + f i
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `abs_norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E]
 (a b : E), |‖a‖ - ‖b‖| ≤ ‖a - b‖
-/
lemma multipliable_norm_one_add_of_summable_norm (hf : Summable fun i ↦ ‖f i‖) :
    Multipliable fun i ↦ ‖1 + f i‖ := by
  conv => enter [1, i]; rw [← sub_add_cancel ‖1 + f i‖ 1, add_comm]
  refine Real.multipliable_one_add_of_summable <| hf.of_norm_bounded (fun i ↦ ?_)
  simpa using abs_norm_sub_norm_le (1 + f i) 1
/-
**Finset.norm_prod_one_add_sub_one_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.norm_prod_one_add_sub_one_le (t : Finset ι) (f : ι -> R) : ‖∏ i in 
t, (1 + f i) - 1‖ <= Real.exp (∑ i in t, ‖f i‖) - 1
参数：t : Finset ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Real.exp_add`：∀ (x y : ℝ), Real.exp (x + y) = Real.exp x * Real.exp y
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 63 条，此处仅展示前 30 条）
-/
lemma Finset.norm_prod_one_add_sub_one_le (t : Finset ι) (f : ι → R) :
    ‖∏ i ∈ t, (1 + f i) - 1‖ ≤ Real.exp (∑ i ∈ t, ‖f i‖) - 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert x t hx IH =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Real.exp_add,
      show (1 + f x) * ∏ i ∈ t, (1 + f i) - 1 =
        (∏ i ∈ t, (1 + f i) - 1) + f x * ∏ x ∈ t, (1 + f x) by ring]
    refine (norm_add_le_of_le IH (norm_mul_le _ _)).trans ?_
    generalize h : Real.exp (∑ i ∈ t, ‖f i‖) = A at ⊢ IH
    rw [sub_add_eq_add_sub, sub_le_sub_iff_right]
    transitivity A + ‖f x‖ * A
    · grw [norm_le_norm_sub_add (∏ x ∈ t, (1 + f x)) 1, IH, norm_one, sub_add_cancel]
    rw [← one_add_mul, add_comm]
    exact mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (h ▸ Real.exp_nonneg _)
/-
**prod_vanishing_of_summable_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：prod_vanishing_of_summable_norm (hf : Summable fun i => ‖f i‖) {ε : Real} 
(hε : 0 < ε) : exists s₂, forall t, Disjoint t s₂ -> ‖∏ i in t, (1 + f i) - 1‖ <
 ε
参数：hf : Summable fun i => ‖f i‖；hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Iio_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Iio a ∈ nhds b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `ContinuousAt.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `ContinuousAt.rexp`：ContinuousAt.rexp (h : ContinuousAt f x) : Continuous
At (fun y => exp (f y)) x
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `Summable.vanishing`：∀ {α : Type u_1} {G : Type u_4} [inst : TopologicalS
pace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   {f : α → G}, Summa
ble f → …
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `Finset.norm_prod_one_add_sub_one_le`：Finset.norm_prod_one_add_sub_one_le
 (t : Finset ι) (f : ι -> R) : ‖∏ i in t, (1 + f i) - 1‖ <= Real.exp (∑ i in t, 
‖f i‖) - 1
-/
lemma prod_vanishing_of_summable_norm (hf : Summable fun i ↦ ‖f i‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ s₂, ∀ t, Disjoint t s₂ → ‖∏ i ∈ t, (1 + f i) - 1‖ < ε := by
  suffices ∃ s, ∀ t, Disjoint t s → Real.exp (∑ i ∈ t, ‖f i‖) - 1 < ε from
    this.imp fun s hs t ht ↦ (t.norm_prod_one_add_sub_one_le _).trans_lt (hs t ht)
  suffices {x | Real.exp x - 1 < ε} ∈ 𝓝 0 from hf.vanishing this
  let f (x) := Real.exp x - 1
  have : Set.Iio ε ∈ nhds (f 0) := by simpa [f] using Iio_mem_nhds hε
  exact ContinuousAt.preimage_mem_nhds (by fun_prop) this

open Finset in
/-- In a complete normed ring, `∏' i, (1 + f i)` is convergent if the sum of real numbers
`∑' i, ‖f i‖` is convergent. -/
/-
**multipliable_one_add_of_summable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multipliable_one_add_of_summable [CompleteSpace R] (hf : Summable fun i =>
 ‖f i‖) : Multipliable fun i => (1 + f i)
参数：hf : Summable fun i => ‖f i‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompleteSpace.complete`：∀ {α : Type u} {inst : UniformSpace α} [self : C
ompleteSpace α] {f : Filter α}, Cauchy f → ∃ x, f ≤ nhds x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.cauchy_iff`：∀ {α : Type u} [inst : PseudoMetricSpace α] {f : Filt
er α},   Cauchy f ↔ f.NeBot ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, dist x y < ε
· 使用定理 `SummationFilter.instNeBotFinsetFilterOfNeBot`：∀ {β : Type u_2} (L : Summ
ationFilter β) [L.NeBot], L.filter.NeBot
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `Multipliable.eventually_bounded_finsetProd`：Multipliable.eventually_boun
ded_finsetProd {v : ι -> Real} (hv : Multipliable v) : exists r₁ > 0, exists s₁,
 forall t, s₁ subseteq t -> ∏ i …
· 使用引理 `multipliable_norm_one_add_of_summable_norm`：multipliable_norm_one_add_of
_summable_norm (hf : Summable fun i => ‖f i‖) : Multipliable fun i => ‖1 + f i‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `prod_vanishing_of_summable_norm`：prod_vanishing_of_summable_norm (hf : S
ummable fun i => ‖f i‖) {ε : Real} (hε : 0 < ε) : exists s₂, forall t, Disjoint 
t s₂ -> ‖∏ i in t, (1…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.union_sdiff_of_subset`：union_sdiff_of_subset (h : s subseteq t) :
 s union t \ s = t
· 使用定理 `Finset.prod_union`：prod_union [DecidableEq ι] (h : Disjoint s₁ s₂) : ∏ x
 in s₁ union s₂, f x = (∏ x in s₁, f x) * ∏ x in s₂, f x
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
（共 92 条，此处仅展示前 30 条）

--- 原说明 ---
In a complete normed ring, `∏' i, (1 + f i)` is convergent if the sum of real nu
mbers
`∑' i, ‖f i‖` is convergent.
-/
lemma multipliable_one_add_of_summable [CompleteSpace R]
    (hf : Summable fun i ↦ ‖f i‖) : Multipliable fun i ↦ (1 + f i) := by
  classical
  refine CompleteSpace.complete <| Metric.cauchy_iff.mpr ⟨by infer_instance, fun ε hε ↦ ?_⟩
  obtain ⟨r₁, hr₁, s₁, hs₁⟩ :=
    (multipliable_norm_one_add_of_summable_norm hf).eventually_bounded_finsetProd
  obtain ⟨s₂, hs₂⟩ := prod_vanishing_of_summable_norm hf (show 0 < ε / (2 * r₁) by positivity)
  simp only [unconditional, Filter.mem_map, mem_atTop_sets, Set.mem_preimage]
  let s := s₁ ∪ s₂
  -- The idea here is that if `s` is a large enough finset, then the product over `s` is bounded
  -- by some `r`, and the product over finsets disjoint from `s` is within `ε / (2 * r)` of 1.
  -- From this it follows that the products over any two finsets containing `s` are within `ε` of
  -- each other.
  -- Here `s₁ ⊆ s` guarantees that the product over `s` is bounded, and `s₂ ⊆ s` guarantees that
  -- the product over terms not in `s` is small.
  refine ⟨Metric.ball (∏ i ∈ s, (1 + f i)) (ε / 2), ⟨s, fun b hb ↦ ?_⟩, ?_⟩
  · rw [← union_sdiff_of_subset hb, prod_union sdiff_disjoint.symm,
      Metric.mem_ball, dist_eq_norm_sub, ← mul_sub_one,
      show ε / 2 = r₁ * (ε / (2 * r₁)) by field]
    apply (norm_mul_le _ _).trans_lt
    refine lt_of_le_of_lt (b := r₁ * ‖∏ x ∈ b \ s, (1 + f x) - 1‖) ?_ ?_
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (Finset.norm_prod_le _ _).trans (hs₁ _ subset_union_left)
    · refine mul_lt_mul_of_pos_left (hs₂ _ ?_) hr₁
      simp [s, sdiff_union_distrib, disjoint_iff_inter_eq_empty]
  · intro x hx y hy
    exact (dist_triangle_right _ _ (∏ i ∈ s, (1 + f i))).trans_lt (add_halves ε ▸ add_lt_add hx hy)
/-
**summable_finsetProd_of_summable_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_finsetProd_of_summable_norm [CompleteSpace R] (hf : Summable (fun
 i => ‖f i‖)) : Summable (fun s => ∏ i in s, f i)
参数：hf : Summable (fun i => ‖f i‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用引理 `summable_finsetProd_of_summable_nonneg`：summable_finsetProd_of_summable_
nonneg {f : ι -> Real} (hf : forall i, 0 <= f i) (hfs : Summable f) : Summable (
fun s : Finset ι => ∏ i in s…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Finset.norm_prod_le`：Finset.norm_prod_le {α : Type*} [NormedCommRing α] 
[NormOneClass α] (s : Finset ι) (f : ι -> α) : ‖∏ i in s, f i‖ <= ∏ i in s, ‖f i
‖
-/
lemma summable_finsetProd_of_summable_norm [CompleteSpace R] (hf : Summable (fun i ↦ ‖f i‖)) :
    Summable (fun s ↦ ∏ i ∈ s, f i) :=
  (summable_finsetProd_of_summable_nonneg (fun _ ↦ norm_nonneg _) hf).of_norm_bounded
    fun _ ↦ Finset.norm_prod_le _ _

@[deprecated (since := "2026-04-08")]
alias summable_finset_prod_of_summable_norm := summable_finsetProd_of_summable_norm
/-
**Summable.summable_log_norm_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Summable.summable_log_norm_one_add (hu : Summable fun n => ‖f n‖) : Summab
le fun i => Real.log ‖1 + f i‖
参数：hu : Summable fun n => ‖f n‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.of_norm`：Summable.of_norm {f : ι -> E} (hf : Summable fun a => 
‖f a‖) : Summable f
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_neg_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b + -b = a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddGroup.toOrderedSub`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LE
 α] [AddRightMono α], OrderedSub α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Summable.congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β}, Summable
 f L…
· 使用引理 `Real.summable_log_one_add_of_summable`：summable_log_one_add_of_summable 
(hf : Summable f) : Summable (fun i => log (1 + f i))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma Summable.summable_log_norm_one_add (hu : Summable fun n ↦ ‖f n‖) :
    Summable fun i ↦ Real.log ‖1 + f i‖ := by
  suffices Summable (‖1 + f ·‖ - 1) from
    (Real.summable_log_one_add_of_summable this).congr (by simp)
  refine .of_norm (hu.of_nonneg_of_le (fun i ↦ by positivity) fun i ↦ ?_)
  simp only [Real.norm_eq_abs, abs_le]
  constructor
  · simpa using norm_add_le (1 + f i) (-f i)
  · simpa [add_comm] using norm_add_le (f i) 1
/-
**tprod_one_add_ne_zero_of_summable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tprod_one_add_ne_zero_of_summable [CompleteSpace R] [NormMulClass R] (hf :
 forall i, 1 + f i != 0) (hu : Summable (‖f ·‖)) : ∏' i : ι, (1 + f i) != 0
参数：hf : forall i, 1 + f i != 0；hu : Summable (‖f ·‖)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `Multipliable.norm_tprod`：∀ {α : Type u_1} {E : Type u_2} [inst : Seminor
medCommRing E] [NormMulClass E] [NormOneClass E] {f : α → E},   Multipliable f →
 ‖∏' (i : α),…
· 使用引理 `multipliable_one_add_of_summable`：multipliable_one_add_of_summable [Comp
leteSpace R] (hf : Summable fun i => ‖f i‖) : Multipliable fun i => (1 + f i)
· 使用引理 `Real.rexp_tsum_eq_tprod`：rexp_tsum_eq_tprod (hfn : forall i, 0 < f i) (h
f : Summable fun i => log (f i)) : rexp (∑' i, log (f i)) = ∏' i, f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `Summable.summable_log_norm_one_add`：Summable.summable_log_norm_one_add (
hu : Summable fun n => ‖f n‖) : Summable fun i => Real.log ‖1 + f i‖
· 使用定理 `Real.exp_ne_zero`：∀ (x : ℝ), Real.exp x ≠ 0
-/
lemma tprod_one_add_ne_zero_of_summable [CompleteSpace R] [NormMulClass R]
    (hf : ∀ i, 1 + f i ≠ 0)
    (hu : Summable (‖f ·‖)) : ∏' i : ι, (1 + f i) ≠ 0 := by
  rw [← norm_ne_zero_iff, Multipliable.norm_tprod]
  · rw [← Real.rexp_tsum_eq_tprod (fun i ↦ norm_pos_iff.mpr <| hf i) hu.summable_log_norm_one_add]
    apply Real.exp_ne_zero
  · exact multipliable_one_add_of_summable hu

end NormedRing

