/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Sums over residue classes

We consider infinite sums over functions `f` on `ℕ`, restricted to a residue class mod `m`.

The main result is `summable_indicator_mod_iff`, which states that when `f : ℕ → ℝ` is
decreasing, then the sum over `f` restricted to any residue class
mod `m ≠ 0` converges if and only if the sum over all of `ℕ` converges.
-/

public section


/-
**Finset.sum_indicator_mod** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Finset.sum_indicator_mod {R : Type*} [AddCommMonoid R] (m : Nat) [NeZero m
] (f : Nat -> R) : f = ∑ a : ZMod m, {n : Nat | (n : ZMod m) = a}.indicator f
参数：m : Nat；f : Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Finset.sum_indicator_mod {R : Type*} [AddCommMonoid R] (m : ℕ) [NeZero m] (f : ℕ → R) :
    f = ∑ a : ZMod m, {n : ℕ | (n : ZMod m) = a}.indicator f := by
  ext n
  simp only [Finset.sum_apply, Set.indicator_apply, Set.mem_ofPred_eq, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte]

set_option backward.isDefEq.respectTransparency false in
open Set in
/-- A sequence `f` with values in an additive topological group `R` is summable on the
residue class of `k` mod `m` if and only if `f (m*n + k)` is summable. -/
/-
**summable_indicator_mod_iff_summable** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_indicator_mod_iff_summable {R : Type*} [AddCommGroup R] [Topologi
calSpace R] [IsTopologicalAddGroup R] (m : Nat) [hm : NeZero m] (k : Nat) (f : N
at -> R) : Summable ({n : Nat | (n : ZMod m) = k}.indicator f) ↔ Summable fun n 
=> f (m * n + k)
参数：m : Nat；k : Nat；f : Nat -> R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Finite.summable_compl_iff`：∀ {α : Type u_1} {β : Type u_2} [inst : A
ddCommGroup α] [inst_1 : TopologicalSpace α] [IsTopologicalAddGroup α]   {f : β 
→ α} {s : Set β}, s…
· 使用定理 `Set.finite_lt_nat`：finite_lt_nat (n : Nat) : Set.Finite { i | i < n }
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.indicator_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 (s t : Set α) (f : α → M),   s.indicator (t.indicator f) = (s ∩ t).indicator f
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Set.mem_of_indicator_ne_zero`：∀ {α : Type u_1} {M : Type u_3} [inst : Ze
ro M] {s : Set α} {f : α → M} {a : α}, s.indicator f a ≠ 0 → a ∈ s
· 使用引理 `Nat.range_mul_add`：Nat.range_mul_add (m k : Nat) : Set.range (fun n : Na
t => m * n + k) = {n : Nat | (n : ZMod m) = k ∧ k <= n}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
A sequence `f` with values in an additive topological group `R` is summable on t
he
residue class of `k` mod `m` if and only if `f (m*n + k)` is summable.
-/
lemma summable_indicator_mod_iff_summable {R : Type*} [AddCommGroup R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] (m : ℕ) [hm : NeZero m] (k : ℕ) (f : ℕ → R) :
    Summable ({n : ℕ | (n : ZMod m) = k}.indicator f) ↔ Summable fun n ↦ f (m * n + k) := by
  trans Summable ({n : ℕ | (n : ZMod m) = k ∧ k ≤ n}.indicator f)
  · rw [← (finite_lt_nat k).summable_compl_iff (f := {n : ℕ | (n : ZMod m) = k}.indicator f)]
    simp only [summable_subtype_iff_indicator, indicator_indicator, inter_comm, ofPred_and,
      compl_ofPred, not_lt]
  · let g : ℕ → ℕ := fun n ↦ m * n + k
    have hg : Function.Injective g := fun m n hmn ↦ by simpa [g, hm.ne] using hmn
    have hg' : ∀ n ∉ range g, {n : ℕ | (n : ZMod m) = k ∧ k ≤ n}.indicator f n = 0 := by
      intro n hn
      contrapose! hn
      exact (Nat.range_mul_add m k).symm ▸ mem_of_indicator_ne_zero hn
    convert (Function.Injective.summable_iff hg hg').symm
    simp only [Function.comp_apply, mem_ofPred_eq, Nat.cast_add, Nat.cast_mul, CharP.cast_eq_zero,
      zero_mul, zero_add, le_add_iff_nonneg_left, zero_le, and_self, indicator_of_mem, g]

/-- If `f : ℕ → ℝ` is decreasing and has a negative term, then `f` is not summable. -/
/-
**not_summable_of_antitone_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_summable_of_antitone_of_neg {f : Nat -> Real} (hf : Antitone f) {n : N
at} (hn : f n < 0) : ¬ Summable f
参数：hf : Antitone f；hn : f n < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tendsto_atTop_zero`：∀ {G : Type u_2} [inst : AddCommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G},   Summable f 
→ Filter.Tendsto …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `abs_pos_of_neg`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrd
er α] [AddLeftMono α] {a : α}, a < 0 → 0 < |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.le_max_left`：∀ (a b : ℕ), a ≤ max a b
· 使用定理 `abs_of_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], a < 0 → |a| = -a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.le_max_right`：∀ (a b : ℕ), b ≤ max a b

--- 原说明 ---
If `f : ℕ → ℝ` is decreasing and has a negative term, then `f` is not summable.
-/
lemma not_summable_of_antitone_of_neg {f : ℕ → ℝ} (hf : Antitone f) {n : ℕ} (hn : f n < 0) :
    ¬ Summable f := by
  intro hs
  have := hs.tendsto_atTop_zero
  simp only [Metric.tendsto_atTop, dist_zero_right, Real.norm_eq_abs] at this
  obtain ⟨N, hN⟩ := this (|f n|) (abs_pos_of_neg hn)
  specialize hN (max n N) (n.le_max_right N)
  contrapose! hN; clear hN
  have H : f (max n N) ≤ f n := hf (n.le_max_left N)
  rwa [abs_of_neg hn, abs_of_neg (H.trans_lt hn), neg_le_neg_iff]

/-- If `f : ℕ → ℝ` is decreasing and has a negative term, then `f` restricted to a residue
/-
**is** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：is nearly impossible to state nicely in terms of `cfcHom` (see `cfcHom_com
p`). An additional advantage of the unbundled approach is that expressions like 
`fun x : R ↦ x⁻¹` are valid arguments to `cfc`, and a bundled continuous counter
part can only make sense when the spectrum of `a` does not contain zero and when
 we have an `⁻¹` operation on the domain.  A reader familiar with C⋆-algebra the
ory may be somewhat surprised at the level of abstraction here. For instance, wh
y not require `A` to be an
参数：see `cfcHom_comp`。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class is not summable. -/
/-
**not_summable_indicator_mod_of_antitone_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：not_summable_indicator_mod_of_antitone_of_neg {m : Nat} [hm : NeZero m] {f
 : Nat -> Real} (hf : Antitone f) {n : Nat} (hn : f n < 0) (k : ZMod m) : ¬ Summ
able ({n : Nat | (n : ZMod m) = k}.indicator f)
参数：hf : Antitone f；hn : f n < 0；k : ZMod m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用引理 `summable_indicator_mod_iff_summable`：summable_indicator_mod_iff_summable
 {R : Type*} [AddCommGroup R] [TopologicalSpace R] [IsTopologicalAddGroup R] (m 
: Nat) [hm : NeZero m] (k…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用引理 `not_summable_of_antitone_of_neg`：not_summable_of_antitone_of_neg {f : Na
t -> Real} (hf : Antitone f) {n : Nat} (hn : f n < 0) : ¬ Summable f
· 使用定理 `Antitone.comp_monotone`：Antitone.comp_monotone (hg : Antitone g) (hf : M
onotone f) : Antitone (g ∘ f)
· 使用定理 `Monotone.add_const`：∀ {α : Type u_1} {β : Type u_2} [inst : Add α] [inst
_1 : Preorder α] [inst_2 : Preorder β] {f : β → α} [AddRightMono α],   Monotone 
f → ∀ (a…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Covariant.monotone_of_const`：Covariant.monotone_of_const [CovariantClass
 M N μ (· <= ·)] (m : M) : Monotone (μ m)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_mul_of_pos_left`：∀ {n : ℕ} (m : ℕ), 0 < n → m ≤ n * m
· 使用定理 `Fin.pos'`：∀ {n : ℕ} [Nonempty (Fin n)], 0 < n
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k

--- 原说明 ---
If `f : ℕ → ℝ` is decreasing and has a negative term, then `f` restricted to a r
esidue
class is not summable.
-/
lemma not_summable_indicator_mod_of_antitone_of_neg {m : ℕ} [hm : NeZero m] {f : ℕ → ℝ}
    (hf : Antitone f) {n : ℕ} (hn : f n < 0) (k : ZMod m) :
    ¬ Summable ({n : ℕ | (n : ZMod m) = k}.indicator f) := by
  rw [← ZMod.natCast_zmod_val k, summable_indicator_mod_iff_summable]
  exact not_summable_of_antitone_of_neg
    (hf.comp_monotone <| (Covariant.monotone_of_const m).add_const k.val) <|
    (hf <| (Nat.le_mul_of_pos_left n Fin.pos').trans <| Nat.le_add_right ..).trans_lt hn

/-- If a decreasing sequence of real numbers is summable on one residue class
modulo `m`, then it is also summable on every other residue class mod `m`. -/
/-
**summable_indicator_mod_iff_summable_indicator_mod** 是 Mathlib 中的一个引理，位于命名空间 ``
。
形式化陈述：summable_indicator_mod_iff_summable_indicator_mod {m : Nat} [NeZero m] {f 
: Nat -> Real} (hf : Antitone f) {k : ZMod m} (l : ZMod m) (hs : Summable ({n : 
Nat | (n : ZMod m) = k}.indicator f)) : Summable ({n : Nat | (n : ZMod m) = l}.i
ndicator f)
参数：hf : Antitone f；l : ZMod m；hs : Summable ({n : Nat | (n : ZMod m) = k}.indica
tor f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ZMod.natCast_val`：natCast_val [NeZero n] (i : ZMod n) : (i.val : R) = ca
st i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ZMod.cast_id'`：cast_id' : (ZMod.cast : ZMod n -> ZMod n) = id
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用引理 `summable_indicator_mod_iff_summable`：summable_indicator_mod_iff_summable
 {R : Type*} [AddCommGroup R] [TopologicalSpace R] [IsTopologicalAddGroup R] (m 
: Nat) [hm : NeZero m] (k…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `Nat.add_le_add`：∀ {a b c d : ℕ}, a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `not_summable_indicator_mod_of_antitone_of_neg`：not_summable_indicator_mo
d_of_antitone_of_neg {m : Nat} [hm : NeZero m] {f : Nat -> Real} (hf : Antitone 
f) {n : Nat} (hn : f n < 0) (k : ZM…

--- 原说明 ---
If a decreasing sequence of real numbers is summable on one residue class
modulo `m`, then it is also summable on every other residue class mod `m`.
-/
lemma summable_indicator_mod_iff_summable_indicator_mod {m : ℕ} [NeZero m] {f : ℕ → ℝ}
    (hf : Antitone f) {k : ZMod m} (l : ZMod m)
    (hs : Summable ({n : ℕ | (n : ZMod m) = k}.indicator f)) :
    Summable ({n : ℕ | (n : ZMod m) = l}.indicator f) := by
  by_cases! hf₀ : ∀ n, 0 ≤ f n -- the interesting case
  · rw [← ZMod.natCast_zmod_val k, summable_indicator_mod_iff_summable] at hs
    have hl : (l.val + m : ZMod m) = l := by
      simp only [ZMod.natCast_val, ZMod.cast_id', id_eq, CharP.cast_eq_zero, add_zero]
    rw [← hl, ← Nat.cast_add, summable_indicator_mod_iff_summable]
    exact hs.of_nonneg_of_le (fun _ ↦ hf₀ _)
      fun _ ↦ hf <| Nat.add_le_add Nat.le.refl (k.val_lt.trans_le <| m.le_add_left l.val).le
  · obtain ⟨n, hn⟩ := hf₀
    exact (not_summable_indicator_mod_of_antitone_of_neg hf hn k hs).elim

/-- A decreasing sequence of real numbers is summable on a residue class
if and only if it is summable. -/
/-
**summable_indicator_mod_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_indicator_mod_iff {m : Nat} [NeZero m] {f : Nat -> Real} (hf : An
titone f) (k : ZMod m) : Summable ({n : Nat | (n : ZMod m) = k}.indicator f) ↔ S
ummable f
参数：hf : Antitone f；k : ZMod m。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sum_indicator_mod`：Finset.sum_indicator_mod {R : Type*} [AddCommM
onoid R] (m : Nat) [NeZero m] (f : Nat -> R) : f = ∑ a : ZMod m, {n : Nat | (n :
 ZMod m) = a}.…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `summable_sum`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Add
CommMonoid α] [inst_1 : TopologicalSpace α]   {L : SummationFilter β} [Continuou
sA…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `summable_indicator_mod_iff_summable_indicator_mod`：summable_indicator_mo
d_iff_summable_indicator_mod {m : Nat} [NeZero m] {f : Nat -> Real} (hf : Antito
ne f) {k : ZMod m} (l : ZMod m) (hs : S…
· 使用定理 `Summable.indicator`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace
 α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace
 α], Sum…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ

--- 原说明 ---
A decreasing sequence of real numbers is summable on a residue class
if and only if it is summable.
-/
lemma summable_indicator_mod_iff {m : ℕ} [NeZero m] {f : ℕ → ℝ} (hf : Antitone f) (k : ZMod m) :
    Summable ({n : ℕ | (n : ZMod m) = k}.indicator f) ↔ Summable f := by
  refine ⟨fun H ↦ ?_, fun H ↦ Summable.indicator H _⟩
  rw [Finset.sum_indicator_mod m f]
  convert!
    summable_sum (s := Finset.univ) fun a _ ↦
      summable_indicator_mod_iff_summable_indicator_mod hf a H
  simp only [Finset.sum_apply]

open ZMod

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is a summable function on `ℕ`, and `0 < N`, then we may compute `∑' n : ℕ, f n` by
summing each residue class mod `N` separately. -/
/-
**Nat.sumByResidueClasses** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Nat.sumByResidueClasses {R : Type*} [AddCommGroup R] [UniformSpace R] [IsU
niformAddGroup R] [CompleteSpace R] [T0Space R] {f : Nat -> R} (hf : Summable f)
 (N : Nat) [NeZero N] : ∑' n, f n = ∑ j : ZMod N, ∑' m, f (j.val + N * m)
参数：hf : Summable f；N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] (e : γ ≃ β)   (f : β → α), ∑' (c : 
γ),…
· 使用定理 `Summable.tsum_prod`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst
 : AddCommGroup α] [inst_1 : UniformSpace α] [IsUniformAddGroup α]   [CompleteSp
ace α] […
· 使用定理 `Summable.comp_injective`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
[inst : UniformSpace α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α]   {f : β
 → α} [Comple…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `tsum_fintype`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {L : SummationFilter β}   [L.LeAtTop] [inst_3 : Fin
ty…
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Nat.residueClassesEquiv.eq_1`：∀ (N : ℕ) [inst : NeZero N],   N.residueCl
assesEquiv =     { toFun := fun n => (↑n, n / N), invFun := fun p => p.1.val + N
 * p.2, left_inv :…
· 使用定理 `Equiv.coe_fn_symm_mk`：∀ {α : Sort u} {β : Sort v} (f : α → β) (g : β → α
) (l : Function.LeftInverse g f) (r : Function.RightInverse g f),   ⇑{ toFun := 
f, invFun …

--- 原说明 ---
If `f` is a summable function on `ℕ`, and `0 < N`, then we may compute `∑' n : ℕ
, f n` by
summing each residue class mod `N` separately.
-/
lemma Nat.sumByResidueClasses {R : Type*} [AddCommGroup R] [UniformSpace R] [IsUniformAddGroup R]
    [CompleteSpace R] [T0Space R] {f : ℕ → R} (hf : Summable f) (N : ℕ) [NeZero N] :
    ∑' n, f n = ∑ j : ZMod N, ∑' m, f (j.val + N * m) := by
  rw [← (residueClassesEquiv N).symm.tsum_eq f, Summable.tsum_prod, tsum_fintype,
    residueClassesEquiv, Equiv.coe_fn_symm_mk]
  exact hf.comp_injective (residueClassesEquiv N).symm.injective
