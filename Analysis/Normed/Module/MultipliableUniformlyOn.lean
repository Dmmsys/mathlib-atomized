/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import Mathlib.Topology.Algebra.IsUniformGroup.Order

/-!
# Uniform convergence of products of functions

We gather some results about the uniform convergence of infinite products, in particular those of
the form `∏' i, (1 + f i x)` for a sequence `f` of complex-valued functions.
-/

public section

open Filter Function Complex Finset Topology

variable {α ι : Type*} {s : Set α} {K : Set α} {u : ι → ℝ}

section Complex

variable {f : ι → α → ℂ}

/-
**TendstoUniformlyOn.comp_cexp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：TendstoUniformlyOn.comp_cexp {p : Filter ι} {g : α -> Complex} (hf : Tends
toUniformlyOn f g p K) (hg : BddAbove <| (fun x => (g x).re) '' K) : TendstoUnif
ormlyOn (cexp ∘ f ·) (cexp ∘ g) p K
参数：hf : TendstoUniformlyOn f g p K；hg : BddAbove <| (fun x => (g x).re) '' K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `TendstoUniformlyOn.eventually_forall_le`：TendstoUniformlyOn.eventually_f
orall_le {u v : β} (huv : u < v) (hf : TendstoUniformlyOn f g p K) (hg : forall 
x in K, g x <= u) : forallᶠ i…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `TendstoUniformlyOn.re`：∀ {α : Type u_1} {ι : Type u_2} {f : ι → α → ℂ} {
p : Filter ι} {g : α → ℂ} {K : Set α},   TendstoUniformlyOn f g p K → TendstoUni
formlyOn (f…
· 使用定理 `UniformContinuousOn.comp_tendstoUniformlyOn_eventually`：UniformContinuou
sOn.comp_tendstoUniformlyOn_eventually {t : Set α} (hF : forallᶠ i in p, forall 
x in t, F i x in s) (hf : forall x in t, f x…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `UniformContinuousOn.cexp`：UniformContinuousOn.cexp (a : Real) : UniformC
ontinuousOn exp {x : Complex | x.re <= a}
-/
lemma TendstoUniformlyOn.comp_cexp {p : Filter ι} {g : α → ℂ}
    (hf : TendstoUniformlyOn f g p K) (hg : BddAbove <| (fun x ↦ (g x).re) '' K) :
    TendstoUniformlyOn (cexp ∘ f ·) (cexp ∘ g) p K := by
  obtain ⟨v, hv⟩ : ∃ v, ∀ x ∈ K, (g x).re ≤ v := hg.imp <| by simp [mem_upperBounds]
  have : ∀ᶠ i in p, ∀ x ∈ K, (f i x).re ≤ v + 1 := hf.re.eventually_forall_le (lt_add_one v) hv
  refine (UniformContinuousOn.cexp _).comp_tendstoUniformlyOn_eventually (by simpa) ?_ hf
  exact fun x hx ↦ (hv x hx).trans (lt_add_one v).le
/-
**Summable.hasSumUniformlyOn_log_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Summable.hasSumUniformlyOn_log_one_add (hu : Summable u) (h : forallᶠ i in
 cofinite, forall x in K, ‖f i x‖ <= u i) : HasSumUniformlyOn (fun i x => log (1
 + f i x)) (fun x => ∑' i, log (1 + f i x)) K
参数：hu : Summable u；h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ <= u i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendstoUniformlyOn_tsum_of_cofinite_eventually`：tendstoUniformlyOn_tsum_
of_cofinite_eventually {ι : Type*} {f : ι -> β -> F} {u : ι -> Real} (hu : Summa
ble u) {s : Set β} (hfu : forallᶠ n …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
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
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Complex.norm_log_one_add_half_le_self`：norm_log_one_add_half_le_self {z 
: Complex} (hz : ‖z‖ <= 1 / 2) : ‖log (1 + z)‖ <= (3 / 2) * ‖z‖
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma Summable.hasSumUniformlyOn_log_one_add (hu : Summable u)
    (h : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i) :
    HasSumUniformlyOn (fun i x ↦ log (1 + f i x)) (fun x ↦ ∑' i, log (1 + f i x)) K := by
  simp only [hasSumUniformlyOn_iff_tendstoUniformlyOn]
  apply tendstoUniformlyOn_tsum_of_cofinite_eventually <| hu.mul_left (3 / 2)
  filter_upwards [h, hu.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi hi' x hx
    using (norm_log_one_add_half_le_self <| (hi x hx).trans hi').trans (by simpa using hi x hx)
/-
**Summable.tendstoUniformlyOn_tsum_nat_log_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Summable.tendstoUniformlyOn_tsum_nat_log_one_add {f : Nat -> α -> Complex}
 {u : Nat -> Real} (hu : Summable u) (h : forallᶠ n in atTop, forall x in K, ‖f 
n x‖ <= u n) : TendstoUniformlyOn (fun n x => ∑ m in Finset.range n, log (1 + f 
m x)) (fun x => ∑' n, log (1 + f n x)) atTop K
参数：hu : Summable u；h : forallᶠ n in atTop, forall x in K, ‖f n x‖ <= u n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSumUniformlyOn.tendstoUniformlyOn_finsetRange`：∀ {α : Type u_1} {β : 
Type u_2} [inst : AddCommMonoid α] {g : β → α} {s : Set β} [inst_1 : UniformSpac
e α]   {f : ℕ → β → α},   HasSumUnifor…
· 使用引理 `Summable.hasSumUniformlyOn_log_one_add`：Summable.hasSumUniformlyOn_log_o
ne_add (hu : Summable u) (h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ <= u
 i) : HasSumUniformlyOn (fun…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
-/
lemma Summable.tendstoUniformlyOn_tsum_nat_log_one_add {f : ℕ → α → ℂ} {u : ℕ → ℝ}
    (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun n x ↦ ∑ m ∈ Finset.range n, log (1 + f m x))
    (fun x ↦ ∑' n, log (1 + f n x)) atTop K := by
  rw [← Nat.cofinite_eq_atTop] at h
  exact (hu.hasSumUniformlyOn_log_one_add h).tendstoUniformlyOn_finsetRange

/-- If `x ↦ ∑' i, log (f i x)` is uniformly convergent on `𝔖`, its sum has bounded-above real part
on each set in `𝔖`, and the functions `f i x` have no zeroes, then  `∏' i, f i x` is uniformly
convergent on `𝔖`.

Note that the non-vanishing assumption is really needed here: if this assumption is dropped then
one obtains a counterexample if `ι = α = ℕ` and `f i x` is `0` if `i = x` and `1` otherwise. -/
/-
**hasProdUniformlyOn_of_clog** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasProdUniformlyOn_of_clog (hf : SummableUniformlyOn (fun i x => log (f i 
x)) s) (hfn : forall x in s, forall i, f i x != 0) (hg : BddAbove <| (fun x => (
∑' i, log (f i x)).re) '' s) : HasProdUniformlyOn f (fun x => ∏' i, f i x) s
参数：hf : SummableUniformlyOn (fun i x => log (f i x)) s；hfn : forall x in s, fora
ll i, f i x != 0；hg : BddAbove <| (fun x => (∑' i, log (f i x)).re) '' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SummableUniformlyOn.exists`：∀ {α : Type u_1} {β : Type u_2} {ι : Type u_
3} [inst : AddCommMonoid α] {f : ι → β → α} {s : Set β}   [inst_1 : UniformSpace
 α], SummableUni…
· 使用定理 `TendstoUniformlyOn.congr`：TendstoUniformlyOn.congr {F' : ι -> α -> β} (h
f : TendstoUniformlyOn F f p s) (hff' : forallᶠ n in p, Set.EqOn (F n) (F' n) s)
 : TendstoUnif…
· 使用引理 `TendstoUniformlyOn.comp_cexp`：TendstoUniformlyOn.comp_cexp {p : Filter ι
} {g : α -> Complex} (hf : TendstoUniformlyOn f g p K) (hg : BddAbove <| (fun x 
=> (g x).re) '' K)…
· 使用定理 `HasSumUniformlyOn.tendstoUniformlyOn`：∀ {α : Type u_1} {β : Type u_2} {ι
 : Type u_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β → α} {s : Set β}   
[inst_1 : UniformSpace α],…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSumUniformlyOn.tsum_eqOn`：∀ {α : Type u_1} {β : Type u_2} {ι : Type u
_3} [inst : AddCommMonoid α] {f : ι → β → α} {g : β → α} {s : Set β}   [inst_1 :
 UniformSpace α] …
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.exp_sum`：exp_sum {α : Type*} (s : Finset α) (f : α -> Complex) :
 exp (∑ x in s, f x) = ∏ x in s, exp (f x)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Complex.exp_log`：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TendstoUniformlyOn.congr_right`：TendstoUniformlyOn.congr_right {g : α ->
 β} (hf : TendstoUniformlyOn F f p s) (hfg : EqOn f g s) : TendstoUniformlyOn F 
g p s
· 使用定理 `Set.EqOn.trans`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ f₃ : 
α → β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₃ s → Set.EqOn f₁ f₃ s
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用定理 `Set.EqOn.comp_left`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : 
Set α} {f₁ f₂ : α → β} {g : β → γ},   Set.EqOn f₁ f₂ s → Set.EqOn (g ∘ f₁) (g ∘ 
f₂) s
· 使用引理 `Complex.cexp_tsum_eq_tprod`：cexp_tsum_eq_tprod (hfn : forall i, f i != 0
) (hf : Summable fun i => log (f i)) : cexp (∑' i, log (f i)) = ∏' i, f i
· 使用定理 `SummableUniformlyOn.summable`：∀ {α : Type u_1} {β : Type u_2} {ι : Type 
u_3} [inst : AddCommMonoid α] {f : ι → β → α} {x : β} {s : Set β}   [inst_1 : Un
iformSpace α], Sum…

--- 原说明 ---
If `x ↦ ∑' i, log (f i x)` is uniformly convergent on `𝔖`, its sum has bounded-a
bove real part
on each set in `𝔖`, and the functions `f i x` have no zeroes, then  `∏' i, f i x
` is uniformly
convergent on `𝔖`.

Note that the non-vanishing assumption is really needed here: if this assumption
 is dropped then
one obtains a counterexample if `ι = α = ℕ` and `f i x` is `0` if `i = x` and `1
` otherwise.
-/
lemma hasProdUniformlyOn_of_clog (hf : SummableUniformlyOn (fun i x ↦ log (f i x)) s)
    (hfn : ∀ x ∈ s, ∀ i, f i x ≠ 0)
    (hg : BddAbove <| (fun x ↦ (∑' i, log (f i x)).re) '' s) :
    HasProdUniformlyOn f (fun x ↦ ∏' i, f i x) s := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn]
  obtain ⟨r, hr⟩ := hf.exists
  suffices H : TendstoUniformlyOn (fun s x ↦ ∏ i ∈ s, f i x) (cexp ∘ r) atTop s by
    refine H.congr_right (hr.tsum_eqOn.comp_left.symm.trans ?_)
    exact fun x hx ↦ (cexp_tsum_eq_tprod (hfn x hx) (hf.summable hx))
  refine (hr.tendstoUniformlyOn.comp_cexp ?_).congr ?_
  · simpa +contextual [← hr.tsum_eqOn _] using hg
  · filter_upwards with s i hi using by simp [exp_sum, fun y ↦ exp_log (hfn i hi y)]
/-
**multipliableUniformlyOn_of_clog** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：multipliableUniformlyOn_of_clog (hf : SummableUniformlyOn (fun i x => log 
(f i x)) s) (hfn : forall x in s, forall i, f i x != 0) (hg : BddAbove <| (fun x
 => (∑' i, log (f i x)).re) '' s) : MultipliableUniformlyOn f s
参数：hf : SummableUniformlyOn (fun i x => log (f i x)) s；hfn : forall x in s, fora
ll i, f i x != 0；hg : BddAbove <| (fun x => (∑' i, log (f i x)).re) '' s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasProdUniformlyOn_of_clog`：hasProdUniformlyOn_of_clog (hf : SummableUni
formlyOn (fun i x => log (f i x)) s) (hfn : forall x in s, forall i, f i x != 0)
 (hg : BddAbove …
-/
lemma multipliableUniformlyOn_of_clog (hf : SummableUniformlyOn (fun i x ↦ log (f i x)) s)
    (hfn : ∀ x ∈ s, ∀ i, f i x ≠ 0)
    (hg : BddAbove <| (fun x ↦ (∑' i, log (f i x)).re) '' s) :
    MultipliableUniformlyOn f s :=
  ⟨_, hasProdUniformlyOn_of_clog hf hfn hg⟩

end Complex

namespace Summable

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R] [TopologicalSpace α]
  {f : ι → α → R}

/-- If a sequence of continuous functions `f i x` on an open compact `K` have norms eventually
bounded by a summable function, then `∏' i, (1 + f i x)` is uniformly convergent on `K`. -/
/-
**Summable.hasProdUniformlyOn_one_add** 是 Mathlib 中的一个引理，位于命名空间 `Summable`。
形式化陈述：hasProdUniformlyOn_one_add (hK : IsCompact K) (hu : Summable u) (h : foral
lᶠ i in cofinite, forall x in K, ‖f i x‖ <= u i) (hcts : forall i, ContinuousOn 
(f i) K) : HasProdUniformlyOn (fun i x => 1 + f i x) (fun x => ∏' i, (1 + f i x)
) K
参数：hK : IsCompact K；hu : Summable u；h : forallᶠ i in cofinite, forall x in K, ‖f
 i x‖ <= u i；hcts : forall i, ContinuousOn (f i) K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `Set.nonempty_coe_sort`：nonempty_coe_sort {s : Set α} : Nonempty ↥s ↔ s.N
onempty
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用引理 `multipliable_one_add_of_summable`：multipliable_one_add_of_summable [Comp
leteSpace R] (hf : Summable fun i => ‖f i‖) : Multipliable fun i => (1 + f i)
· 使用定理 `ContinuousMap.instNormOneClassOfNonempty`：∀ {α : Type u_1} {E : Type u_3
} [inst : TopologicalSpace α] [inst_1 : CompactSpace α]   [inst_2 : SeminormedAd
dCommGroup E] [Nonempty α] [in…
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `Summable.of_norm_bounded_eventually`：Summable.of_norm_bounded_eventually
 {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i in cofinite, ‖f i
‖ <= g i) : Summable f
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
If a sequence of continuous functions `f i x` on an open compact `K` have norms 
eventually
bounded by a summable function, then `∏' i, (1 + f i x)` is uniformly convergent
 on `K`.
-/
lemma hasProdUniformlyOn_one_add (hK : IsCompact K) (hu : Summable u)
    (h : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i) (hcts : ∀ i, ContinuousOn (f i) K) :
    HasProdUniformlyOn (fun i x ↦ 1 + f i x) (fun x ↦ ∏' i, (1 + f i x)) K := by
  simp only [hasProdUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  by_cases hKe : K = ∅
  · simp [TendstoUniformly, hKe]
  · have hCK : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have hne : Nonempty K := by rwa [Set.nonempty_coe_sort, Set.nonempty_iff_ne_empty]
    let f' i : C(K, R) := ⟨_, continuousOn_iff_continuous_domRestrict.mp (hcts i)⟩
    have hf'_bd : ∀ᶠ i in cofinite, ‖f' i‖ ≤ u i := by
      simp only [ContinuousMap.norm_le_of_nonempty]
      filter_upwards [h] with i hi using fun x ↦ hi x x.2
    have hM : Multipliable fun i ↦ 1 + f' i :=
      multipliable_one_add_of_summable (hu.of_norm_bounded_eventually (by simpa using hf'_bd))
    convert! ContinuousMap.tendsto_iff_tendstoUniformly.mp hM.hasProd
    · simp [f']
    · exact funext fun k ↦ ContinuousMap.tprod_apply hM k
/-
**Summable.multipliableUniformlyOn_one_add** 是 Mathlib 中的一个引理，位于命名空间 `Summable`。
形式化陈述：multipliableUniformlyOn_one_add (hK : IsCompact K) (hu : Summable u) (h : 
forallᶠ i in cofinite, forall x in K, ‖f i x‖ <= u i) (hcts : forall i, Continuo
usOn (f i) K) : MultipliableUniformlyOn (fun i x => 1 + f i x) K
参数：hK : IsCompact K；hu : Summable u；h : forallᶠ i in cofinite, forall x in K, ‖f
 i x‖ <= u i；hcts : forall i, ContinuousOn (f i) K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Summable.hasProdUniformlyOn_one_add`：hasProdUniformlyOn_one_add (hK : Is
Compact K) (hu : Summable u) (h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ 
<= u i) (hcts : forall i,…
-/
lemma multipliableUniformlyOn_one_add (hK : IsCompact K) (hu : Summable u)
    (h : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i) (hcts : ∀ i, ContinuousOn (f i) K) :
    MultipliableUniformlyOn (fun i x ↦ 1 + f i x) K :=
  ⟨_, hasProdUniformlyOn_one_add hK hu h hcts⟩

/-- This is a version of `hasProdUniformlyOn_one_add` for sequences indexed by `ℕ`. -/
/-
**Summable.hasProdUniformlyOn_nat_one_add** 是 Mathlib 中的一个引理，位于命名空间 `Summable`。
形式化陈述：hasProdUniformlyOn_nat_one_add {f : Nat -> α -> R} (hK : IsCompact K) {u :
 Nat -> Real} (hu : Summable u) (h : forallᶠ n in atTop, forall x in K, ‖f n x‖ 
<= u n) (hcts : forall n, ContinuousOn (f n) K) : HasProdUniformlyOn (fun n x =>
 1 + f n x) (fun x => ∏' i, (1 + f i x)) K
参数：hK : IsCompact K；hu : Summable u；h : forallᶠ n in atTop, forall x in K, ‖f n 
x‖ <= u n；hcts : forall n, ContinuousOn (f n) K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Summable.hasProdUniformlyOn_one_add`：hasProdUniformlyOn_one_add (hK : Is
Compact K) (hu : Summable u) (h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ 
<= u i) (hcts : forall i,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop

--- 原说明 ---
This is a version of `hasProdUniformlyOn_one_add` for sequences indexed by `ℕ`.
-/
lemma hasProdUniformlyOn_nat_one_add {f : ℕ → α → R} (hK : IsCompact K) {u : ℕ → ℝ}
    (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    HasProdUniformlyOn (fun n x ↦ 1 + f n x) (fun x ↦ ∏' i, (1 + f i x)) K :=
  hasProdUniformlyOn_one_add hK hu (Nat.cofinite_eq_atTop ▸ h) hcts
/-
**Summable.multipliableUniformlyOn_nat_one_add** 是 Mathlib 中的一个引理，位于命名空间 `Summab
le`。
形式化陈述：multipliableUniformlyOn_nat_one_add {f : Nat -> α -> R} (hK : IsCompact K)
 {u : Nat -> Real} (hu : Summable u) (h : forallᶠ n in atTop, forall x in K, ‖f 
n x‖ <= u n) (hcts : forall n, ContinuousOn (f n) K) : MultipliableUniformlyOn (
fun n x => 1 + f n x) K
参数：hK : IsCompact K；hu : Summable u；h : forallᶠ n in atTop, forall x in K, ‖f n 
x‖ <= u n；hcts : forall n, ContinuousOn (f n) K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Summable.hasProdUniformlyOn_nat_one_add`：hasProdUniformlyOn_nat_one_add 
{f : Nat -> α -> R} (hK : IsCompact K) {u : Nat -> Real} (hu : Summable u) (h : 
forallᶠ n in atTop, forall x …
-/
lemma multipliableUniformlyOn_nat_one_add {f : ℕ → α → R} (hK : IsCompact K)
    {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    MultipliableUniformlyOn (fun n x ↦ 1 + f n x) K :=
  ⟨_, hasProdUniformlyOn_nat_one_add hK hu h hcts⟩

section LocallyCompactSpace

variable [LocallyCompactSpace α]

/-- If a sequence of continuous functions `f i x` on an open subset `K` have norms eventually
bounded by a summable function, then `∏' i, (1 + f i x)` is locally uniformly convergent on `K`. -/
/-
**Summable.hasProdLocallyUniformlyOn_one_add** 是 Mathlib 中的一个引理，位于命名空间 `Summable
`。
形式化陈述：hasProdLocallyUniformlyOn_one_add (hK : IsOpen K) (hu : Summable u) (h : f
orallᶠ i in cofinite, forall x in K, ‖f i x‖ <= u i) (hcts : forall i, Continuou
sOn (f i) K) : HasProdLocallyUniformlyOn (fun i x => 1 + f i x) (fun x => ∏' i, 
(1 + f i x)) K
参数：hK : IsOpen K；hu : Summable u；h : forallᶠ i in cofinite, forall x in K, ‖f i 
x‖ <= u i；hcts : forall i, ContinuousOn (f i) K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `hasProdLocallyUniformlyOn_of_forall_compact`：hasProdLocallyUniformlyOn_o
f_forall_compact (hs : IsOpen s) [LocallyCompactSpace β] (h : forall K subseteq 
s, IsCompact K -> HasProdUniforml…
· 使用引理 `Summable.hasProdUniformlyOn_one_add`：hasProdUniformlyOn_one_add (hK : Is
Compact K) (hu : Summable u) (h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ 
<= u i) (hcts : forall i,…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t

--- 原说明 ---
If a sequence of continuous functions `f i x` on an open subset `K` have norms e
ventually
bounded by a summable function, then `∏' i, (1 + f i x)` is locally uniformly co
nvergent on `K`.
-/
lemma hasProdLocallyUniformlyOn_one_add (hK : IsOpen K) (hu : Summable u)
    (h : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i) (hcts : ∀ i, ContinuousOn (f i) K) :
    HasProdLocallyUniformlyOn (fun i x ↦ 1 + f i x) (fun x ↦ ∏' i, (1 + f i x)) K := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hK
  refine fun S hS hC ↦ hasProdUniformlyOn_one_add hC hu ?_ fun i ↦ (hcts i).mono hS
  filter_upwards [h] with i hi a ha using hi a (hS ha)
/-
**Summable.multipliableLocallyUniformlyOn_one_add** 是 Mathlib 中的一个引理，位于命名空间 `Sum
mable`。
形式化陈述：multipliableLocallyUniformlyOn_one_add (hK : IsOpen K) (hu : Summable u) (
h : forallᶠ i in cofinite, forall x in K, ‖f i x‖ <= u i) (hcts : forall i, Cont
inuousOn (f i) K) : MultipliableLocallyUniformlyOn (fun i x => 1 + f i x) K
参数：hK : IsOpen K；hu : Summable u；h : forallᶠ i in cofinite, forall x in K, ‖f i 
x‖ <= u i；hcts : forall i, ContinuousOn (f i) K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Summable.hasProdLocallyUniformlyOn_one_add`：hasProdLocallyUniformlyOn_on
e_add (hK : IsOpen K) (hu : Summable u) (h : forallᶠ i in cofinite, forall x in 
K, ‖f i x‖ <= u i) (hcts : foral…
-/
lemma multipliableLocallyUniformlyOn_one_add (hK : IsOpen K) (hu : Summable u)
    (h : ∀ᶠ i in cofinite, ∀ x ∈ K, ‖f i x‖ ≤ u i) (hcts : ∀ i, ContinuousOn (f i) K) :
    MultipliableLocallyUniformlyOn (fun i x ↦ 1 + f i x) K :=
  ⟨_, hasProdLocallyUniformlyOn_one_add hK hu h hcts⟩

/-- This is a version of `hasProdLocallyUniformlyOn_one_add` for sequences indexed by `ℕ`. -/
/-
**Summable.hasProdLocallyUniformlyOn_nat_one_add** 是 Mathlib 中的一个引理，位于命名空间 `Summ
able`。
形式化陈述：hasProdLocallyUniformlyOn_nat_one_add {f : Nat -> α -> R} (hK : IsOpen K) 
{u : Nat -> Real} (hu : Summable u) (h : forallᶠ n in atTop, forall x in K, ‖f n
 x‖ <= u n) (hcts : forall n, ContinuousOn (f n) K) : HasProdLocallyUniformlyOn 
(fun n x => 1 + f n x) (fun x => ∏' i, (1 + f i x)) K
参数：hK : IsOpen K；hu : Summable u；h : forallᶠ n in atTop, forall x in K, ‖f n x‖ 
<= u n；hcts : forall n, ContinuousOn (f n) K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Summable.hasProdLocallyUniformlyOn_one_add`：hasProdLocallyUniformlyOn_on
e_add (hK : IsOpen K) (hu : Summable u) (h : forallᶠ i in cofinite, forall x in 
K, ‖f i x‖ <= u i) (hcts : foral…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop

--- 原说明 ---
This is a version of `hasProdLocallyUniformlyOn_one_add` for sequences indexed b
y `ℕ`.
-/
lemma hasProdLocallyUniformlyOn_nat_one_add {f : ℕ → α → R} (hK : IsOpen K) {u : ℕ → ℝ}
    (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    HasProdLocallyUniformlyOn (fun n x ↦ 1 + f n x) (fun x ↦ ∏' i, (1 + f i x)) K :=
  hasProdLocallyUniformlyOn_one_add hK hu (Nat.cofinite_eq_atTop ▸ h) hcts
/-
**Summable.multipliableLocallyUniformlyOn_nat_one_add** 是 Mathlib 中的一个引理，位于命名空间 
`Summable`。
形式化陈述：multipliableLocallyUniformlyOn_nat_one_add {f : Nat -> α -> R} (hK : IsOpe
n K) {u : Nat -> Real} (hu : Summable u) (h : forallᶠ n in atTop, forall x in K,
 ‖f n x‖ <= u n) (hcts : forall n, ContinuousOn (f n) K) : MultipliableLocallyUn
iformlyOn (fun n x => 1 + f n x) K
参数：hK : IsOpen K；hu : Summable u；h : forallᶠ n in atTop, forall x in K, ‖f n x‖ 
<= u n；hcts : forall n, ContinuousOn (f n) K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Summable.hasProdLocallyUniformlyOn_nat_one_add`：hasProdLocallyUniformlyO
n_nat_one_add {f : Nat -> α -> R} (hK : IsOpen K) {u : Nat -> Real} (hu : Summab
le u) (h : forallᶠ n in atTop, foral…
-/
lemma multipliableLocallyUniformlyOn_nat_one_add {f : ℕ → α → R} (hK : IsOpen K) {u : ℕ → ℝ}
    (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n)
    (hcts : ∀ n, ContinuousOn (f n) K) :
    MultipliableLocallyUniformlyOn (fun n x ↦ 1 + f n x) K :=
  ⟨_, hasProdLocallyUniformlyOn_nat_one_add hK hu h hcts⟩

end LocallyCompactSpace

end Summable

