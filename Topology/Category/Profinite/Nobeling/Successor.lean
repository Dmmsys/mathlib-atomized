/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Topology.Category.Profinite.Nobeling.Basic

/-!
# The successor case in the induction for Nöbeling's theorem

Here we assume that `o` is an ordinal such that `contained C (o+1)` and `o < I`. The element in `I`
corresponding to `o` is called `term I ho`, but in this informal docstring we refer to it simply as
`o`.

This section follows the proof in [scholze2019condensed] quite closely. A translation of the
notation there is as follows:

```
[scholze2019condensed]                  | This file
`S₀`                                    |`C0`
`S₁`                                    |`C1`
`\overline{S}`                          |`π C (ord I · < o)
`\overline{S}'`                         |`C'`
The left map in the exact sequence      |`πs`
The right map in the exact sequence     |`Linear_CC'`
```

When comparing the proof of the successor case in Theorem 5.4 in [scholze2019condensed] with this
proof, one should read the phrase "is a basis" as "is linearly independent". Also, the short exact
sequence in [scholze2019condensed] is only proved to be left exact here (indeed, that is enough
since we are only proving linear independence).

This section is split into two sections. The first one, `ExactSequence` defines the left exact
sequence mentioned in the previous paragraph (see `succ_mono` and `succ_exact`). It corresponds to
the penultimate paragraph of the proof in [scholze2019condensed]. The second one, `GoodProducts`
corresponds to the last paragraph in the proof in [scholze2019condensed].

For the overall proof outline see `Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## Main definitions

The main definitions in the section `ExactSequence` are all just notation explained in the table
above.

The main definitions in the section `GoodProducts` are as follows:

* `MaxProducts`: the set of good products that contain the ordinal `o` (since we have
  `contained C (o+1)`, these all start with `o`).

* `GoodProducts.sum_equiv`: the equivalence between `GoodProducts C` and the disjoint union of
  `MaxProducts C` and `GoodProducts (π C (ord I · < o))`.

## Main results

* The main results in the section `ExactSequence` are `succ_mono` and `succ_exact` which together
  say that the sequence given by `πs` and `Linear_CC'` is left exact:
  ```
                                              f                        g
  0 --→ LocallyConstant (π C (ord I · < o)) ℤ --→ LocallyConstant C ℤ --→ LocallyConstant C' ℤ
  ```
  where `f` is `πs` and `g` is `Linear_CC'`.

The main results in the section `GoodProducts` are as follows:

* `Products.max_eq_eval` says that the linear map on the right in the exact sequence, i.e.
  `Linear_CC'`, takes the evaluation of a term of `MaxProducts` to the evaluation of the
  corresponding list with the leading `o` removed.

* `GoodProducts.maxTail_isGood` says that removing the leading `o` from a term of `MaxProducts C`
  yields a list which `isGood` with respect to `C'`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I → Bool)) [LinearOrder I] [WellFoundedLT I]
  {o : Ordinal} (hC : IsClosed C) (hsC : contained C (Order.succ o))
  (ho : o < Ordinal.type (· < · : I → I → Prop))

section ExactSequence

/-- The subset of `C` consisting of those elements whose `o`-th entry is `false`. -/
/-
**Profinite.NobelingProof.C0** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof`
。
形式化陈述：C0
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2

--- 原说明 ---
The subset of `C` consisting of those elements whose `o`-th entry is `false`.
-/
def C0 := C ∩ {f | f (term I ho) = false}

/-- The subset of `C` consisting of those elements whose `o`-th entry is `true`. -/
/-
**Profinite.NobelingProof.C1** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof`
。
形式化陈述：C1
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2

--- 原说明 ---
The subset of `C` consisting of those elements whose `o`-th entry is `true`.
-/
def C1 := C ∩ {f | f (term I ho) = true}

include hC in
/-
**Profinite.NobelingProof.isClosed_C0** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobel
ingProof`。
形式化陈述：isClosed_C0 : IsClosed (C0 C ho)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_discrete`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Discret
eTopology α] (s : Set α), IsClosed s
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
-/
theorem isClosed_C0 : IsClosed (C0 C ho) := by
  refine hC.inter ?_
  have h : Continuous (fun (f : I → Bool) ↦ f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (t := {false}) (isClosed_discrete _)

include hC in
/-
**Profinite.NobelingProof.isClosed_C1** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobel
ingProof`。
形式化陈述：isClosed_C1 : IsClosed (C1 C ho)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `isClosed_discrete`：∀ {α : Type u_1} [inst : TopologicalSpace α] [Discret
eTopology α] (s : Set α), IsClosed s
· 使用定理 `instDiscreteTopologyBool`：DiscreteTopology Bool
-/
theorem isClosed_C1 : IsClosed (C1 C ho) := by
  refine hC.inter ?_
  have h : Continuous (fun (f : I → Bool) ↦ f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (t := {true}) (isClosed_discrete _)
/-
**Profinite.NobelingProof.contained_C1** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobe
lingProof`。
形式化陈述：contained_C1 : contained (π (C1 C ho) (ord I · < o)) o
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Profinite.NobelingProof.contained_proj`：contained_proj (o : Ordinal) : c
ontained (π C (ord I · < o)) o
-/
theorem contained_C1 : contained (π (C1 C ho) (ord I · < o)) o :=
  contained_proj _ _
/-
**Profinite.NobelingProof.union_C0C1_eq** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nob
elingProof`。
形式化陈述：union_C0C1_eq : (C0 C ho) union (C1 C ho) = C
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Bool.dichotomy`：dichotomy (b : Bool) : b = false ∨ b = true
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem union_C0C1_eq : (C0 C ho) ∪ (C1 C ho) = C := by
  ext x
  simp only [C0, C1, Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq,
    ← and_or_left, and_iff_left_iff_imp, Bool.dichotomy (x (term I ho)), implies_true]

/--
The intersection of `C0` and the projection of `C1`. We will apply the inductive hypothesis to
this set.
-/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Profinite.NobelingProof.C'** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof`
。
形式化陈述：C'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
-/
noncomputable def C' := C0 C ho ∩ π (C1 C ho) (ord I · < o)

include hC in
/-
**Profinite.NobelingProof.isClosed_C'** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobel
ingProof`。
形式化陈述：isClosed_C' : IsClosed (C' C ho)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `Profinite.NobelingProof.isClosed_C0`：isClosed_C0 : IsClosed (C0 C ho)
· 使用定理 `Profinite.NobelingProof.isClosed_proj`：isClosed_proj (o : Ordinal) (hC :
 IsClosed C) : IsClosed (π C (ord I · < o))
· 使用定理 `Profinite.NobelingProof.isClosed_C1`：isClosed_C1 : IsClosed (C1 C ho)
-/
theorem isClosed_C' : IsClosed (C' C ho) :=
  IsClosed.inter (isClosed_C0 _ hC _) (isClosed_proj _ _ (isClosed_C1 _ hC _))
/-
**Profinite.NobelingProof.contained_C'** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobe
lingProof`。
形式化陈述：contained_C' : contained (C' C ho) o
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Profinite.NobelingProof.contained_C1`：contained_C1 : contained (π (C1 C 
ho) (ord I · < o)) o
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem contained_C' : contained (C' C ho) o := fun f hf i hi ↦ contained_C1 C ho f hf.2 i hi

variable (o)

/-- Swapping the `o`-th coordinate to `true`. -/
noncomputable
/-
**Profinite.NobelingProof.SwapTrue** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobeling
Proof`。
形式化陈述：SwapTrue : (I -> Bool) -> I -> Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def SwapTrue : (I → Bool) → I → Bool :=
  fun f i ↦ if ord I i = o then true else f i
/-
**Profinite.NobelingProof.continuous_swapTrue** 是 Mathlib 中的一个定理，位于命名空间 `Profini
te.NobelingProof`。
形式化陈述：continuous_swapTrue : Continuous (SwapTrue o : (I -> Bool) -> I -> Bool)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_pi`：continuous_pi (f : X → α → Y) (hf : ∀ a, Continuous (f x 
a)) : Continuous (fun x a ↦ f x a)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_bot`：continuous_bot {t : TopologicalSpace β} : Continuous[⊥, 
t] f
· 使用定理 `continuous_apply`：continuous_apply (a : α) : Continuous (fun f : (α → X)
 ↦ f a)
-/
theorem continuous_swapTrue : Continuous (SwapTrue o : (I → Bool) → I → Bool) := by
  dsimp +unfoldPartialApp [SwapTrue]
  apply continuous_pi
  intro i
  apply Continuous.comp'
  · apply continuous_bot
  · apply continuous_apply

variable {o}

include hsC in
/-
**Profinite.NobelingProof.swapTrue_mem_C1** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.N
obelingProof`。
形式化陈述：swapTrue_mem_C1 (f : π (C1 C ho) (ord I · < o)) : SwapTrue o f.val in C1 C
 ho
参数：f : π (C1 C ho) (ord I · < o)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Profinite.NobelingProof.ord_term`：ord_term {o : Ordinal} (ho : o < Ordin
al.type ((· < ·) : I -> I -> Prop)) (i : I) : ord I i = o ↔ term I ho = i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem swapTrue_mem_C1 (f : π (C1 C ho) (ord I · < o)) :
    SwapTrue o f.val ∈ C1 C ho := by
  obtain ⟨f, g, hg, rfl⟩ := f
  convert! hg
  dsimp +unfoldPartialApp [SwapTrue]
  ext i
  split_ifs with h
  · rw [ord_term ho] at h
    simpa only [← h] using hg.2.symm
  · simp only [Proj, ite_eq_left_iff, not_lt, @eq_comm _ false, ← Bool.not_eq_true]
    specialize hsC g hg.1 i
    intro h'
    contrapose! hsC
    exact ⟨hsC, Order.succ_le_of_lt (h'.lt_of_ne' h)⟩

/-- The first way to map `C'` into `C`. -/
/-
**Profinite.NobelingProof.CC'** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof
`。
形式化陈述：CC'₀ : C' C ho -> C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first way to map `C'` into `C`.
-/
def CC'₀ : C' C ho → C := fun g ↦ ⟨g.val,g.prop.1.1⟩

/-- The second way to map `C'` into `C`. -/
noncomputable
/-
**Profinite.NobelingProof.CC'** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.NobelingProof
`。
形式化陈述：CC'₀ : C' C ho -> C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def CC'₁ : C' C ho → C :=
  fun g ↦ ⟨SwapTrue o g.val, (swapTrue_mem_C1 C hsC ho ⟨g.val,g.prop.2⟩).1⟩
/-
**Profinite.NobelingProof.continuous_CC'** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.No
belingProof`。
形式化陈述：continuous_CC'₀ : Continuous (CC'₀ C ho)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem continuous_CC'₀ : Continuous (CC'₀ C ho) := Continuous.subtype_mk continuous_subtype_val _
/-
**Profinite.NobelingProof.continuous_CC'** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.No
belingProof`。
形式化陈述：continuous_CC'₀ : Continuous (CC'₀ C ho)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem continuous_CC'₁ : Continuous (CC'₁ C hsC ho) :=
  Continuous.subtype_mk (Continuous.comp (continuous_swapTrue o) continuous_subtype_val) _

/-- The `ℤ`-linear map induced by precomposing with `CC'₀` -/
noncomputable
/-
**Profinite.NobelingProof.Linear_CC'** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobeli
ngProof`。
形式化陈述：Linear_CC'₀ : LocallyConstant C Int ->ₗ[Int] LocallyConstant (C' C ho) Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
-/
def Linear_CC'₀ : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
  LocallyConstant.comapₗ ℤ ⟨(CC'₀ C ho), (continuous_CC'₀ C ho)⟩

/-- The `ℤ`-linear map induced by precomposing with `CC'₁` -/
noncomputable
/-
**Profinite.NobelingProof.Linear_CC'** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobeli
ngProof`。
形式化陈述：Linear_CC'₀ : LocallyConstant C Int ->ₗ[Int] LocallyConstant (C' C ho) Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
-/
def Linear_CC'₁ : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
  LocallyConstant.comapₗ ℤ ⟨(CC'₁ C hsC ho), (continuous_CC'₁ C hsC ho)⟩

/-- The difference between `Linear_CC'₁` and `Linear_CC'₀`. -/
noncomputable
/-
**Profinite.NobelingProof.Linear_CC'** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nobeli
ngProof`。
形式化陈述：Linear_CC'₀ : LocallyConstant C Int ->ₗ[Int] LocallyConstant (C' C ho) Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
-/
def Linear_CC' : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
  Linear_CC'₁ C hsC ho - Linear_CC'₀ C ho

set_option backward.defeqAttrib.useBackward true in
/-
**Profinite.NobelingProof.CC_comp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobe
lingProof`。
形式化陈述：CC_comp_zero : forall y, (Linear_CC' C hsC ho) ((πs C o) y) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_ctx_congr`：if_ctx_congr (h_c : P ↔ Q) (h_t : Q -> x = u) (h_e : ¬Q ->
 y = v) : ite P x y = ite Q u v
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem CC_comp_zero : ∀ y, (Linear_CC' C hsC ho) ((πs C o) y) = 0 := by
  intro y
  ext x
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁, LocallyConstant.sub_apply]
  simp only [sub_eq_zero]
  congr 1
  ext i
  dsimp [CC'₀, CC'₁, ProjRestrict, Proj]
  apply if_ctx_congr Iff.rfl _ (fun _ ↦ rfl)
  simp only [SwapTrue, ite_eq_right_iff]
  intro h₁ h₂
  exact (h₁.ne h₂).elim

include hsC in
/-
**Profinite.NobelingProof.C0_projOrd** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobeli
ngProof`。
形式化陈述：C0_projOrd {x : I -> Bool} (hx : x in C0 C ho) : Proj (ord I · < o) x = x
参数：hx : x in C0 C ho。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.lt_or_eq`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a < b ∨ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Profinite.NobelingProof.ord_term`：ord_term {o : Ordinal} (ho : o < Ordin
al.type ((· < ·) : I -> I -> Prop)) (i : I) : ord I i = o ↔ term I ho = i
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem C0_projOrd {x : I → Bool} (hx : x ∈ C0 C ho) : Proj (ord I · < o) x = x := by
  ext i
  simp only [Proj, ite_eq_left_iff, not_lt]
  intro hi
  rcases hi.lt_or_eq with hi | hi
  · specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC hi).symm
  · simp only [C0, Set.mem_inter_iff, Set.mem_ofPred_eq] at hx
    rw [eq_comm, ord_term ho] at hi
    rw [← hx.2, hi]

include hsC in
/-
**Profinite.NobelingProof.C1_projOrd** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobeli
ngProof`。
形式化陈述：C1_projOrd {x : I -> Bool} (hx : x in C1 C ho) : SwapTrue o (Proj (ord I ·
 < o) x) = x
参数：hx : x in C1 C ho。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Profinite.NobelingProof.ord_term`：ord_term {o : Ordinal} (ho : o < Ordin
al.type ((· < ·) : I -> I -> Prop)) (i : I) : ord I i = o ↔ term I ho = i
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem C1_projOrd {x : I → Bool} (hx : x ∈ C1 C ho) : SwapTrue o (Proj (ord I · < o) x) = x := by
  ext i
  dsimp [SwapTrue, Proj]
  split_ifs with hi h
  · rw [ord_term ho] at hi
    rw [← hx.2, hi]
  · rfl
  · simp only [not_lt] at h
    have h' : o < ord I i := lt_of_le_of_ne h (Ne.symm hi)
    specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC h').symm

set_option backward.isDefEq.respectTransparency.types false in
include hC in
/-
**Profinite.NobelingProof.CC_exact** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobeling
Proof`。
形式化陈述：CC_exact {f : LocallyConstant C Int} (hf : Linear_CC' C hsC ho f = 0) : ex
ists y, πs C o y = f
参数：hf : Linear_CC' C hsC ho f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `continuous_induced_dom`：continuous_induced_dom {t : TopologicalSpace β} 
: Continuous[induced f t, t] f
· 使用定理 `Profinite.NobelingProof.swapTrue_mem_C1`：swapTrue_mem_C1 (f : π (C1 C ho
) (ord I · < o)) : SwapTrue o f.val in C1 C ho
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Profinite.NobelingProof.continuous_swapTrue`：continuous_swapTrue : Conti
nuous (SwapTrue o : (I -> Bool) -> I -> Bool)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.C0_projOrd`：C0_projOrd {x : I -> Bool} (hx : x i
n C0 C ho) : Proj (ord I · < o) x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.union_C0C1_eq`：union_C0C1_eq : (C0 C ho) union (
C1 C ho) = C
· 使用定理 `Profinite.NobelingProof.isClosed_C0`：isClosed_C0 : IsClosed (C0 C ho)
· 使用定理 `Profinite.NobelingProof.isClosed_proj`：isClosed_proj (o : Ordinal) (hC :
 IsClosed C) : IsClosed (π C (ord I · < o))
· 使用定理 `Profinite.NobelingProof.isClosed_C1`：isClosed_C1 : IsClosed (C1 C ho)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Profinite.NobelingProof.continuous_CC'₁`：∀ {I : Type u} (C : Set (I → Bo
ol)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (hsC 
: Profinite.NobelingProof.con…
· 使用定理 `Profinite.NobelingProof.continuous_CC'₀`：∀ {I : Type u} (C : Set (I → Bo
ol)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (ho :
 o < Ordinal.type fun x1 x2 =…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Profinite.NobelingProof.πs_apply_apply`：∀ {I : Type u} (C : Set (I → Boo
l)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] (o : Ordinal.{u})   (g : L
ocallyConstant ↑(Profinite.N…
· 使用定理 `LocallyConstant.piecewise'_apply_left`：∀ {X : Type u_1} {Z : Type u_3} [
inst : TopologicalSpace X] {C₀ C₁ C₂ : Set X} (h₀ : C₀ ⊆ C₁ ∪ C₂) (h₁ : IsClosed
 C₁)   (h₂ : IsClosed C₂) (…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 35 条，此处仅展示前 30 条）
-/
theorem CC_exact {f : LocallyConstant C ℤ} (hf : Linear_CC' C hsC ho f = 0) :
    ∃ y, πs C o y = f := by
  classical
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁] at hf
  simp only [sub_eq_zero, ← LocallyConstant.coe_inj] at hf
  let C₀C : C0 C ho → C := fun x ↦ ⟨x.val, x.prop.1⟩
  have h₀ : Continuous C₀C := Continuous.subtype_mk continuous_induced_dom _
  let C₁C : π (C1 C ho) (ord I · < o) → C :=
    fun x ↦ ⟨SwapTrue o x.val, (swapTrue_mem_C1 C hsC ho x).1⟩
  have h₁ : Continuous C₁C := Continuous.subtype_mk
    ((continuous_swapTrue o).comp continuous_subtype_val) _
  refine ⟨LocallyConstant.piecewise' ?_ (isClosed_C0 C hC ho)
      (isClosed_proj _ o (isClosed_C1 C hC ho)) (f.comap ⟨C₀C, h₀⟩) (f.comap ⟨C₁C, h₁⟩) ?_, ?_⟩
  · rintro _ ⟨y, hyC, rfl⟩
    simp only [Set.mem_union]
    rw [← union_C0C1_eq C ho] at hyC
    refine hyC.imp (fun hyC ↦ ?_) (fun hyC ↦ ⟨y, hyC, rfl⟩)
    rwa [C0_projOrd C hsC ho hyC]
  · intro x hx
    simpa only [h₀, h₁, LocallyConstant.coe_comap] using! (congrFun hf ⟨x, hx⟩).symm
  · ext ⟨x, hx⟩
    rw [← union_C0C1_eq C ho] at hx
    rcases hx with hx₀ | hx₁
    · have hx₀' : ProjRestrict C (ord I · < o) ⟨x, hx⟩ = x := by
        simpa only [ProjRestrict, Set.MapsTo.val_restrict_apply] using! C0_projOrd C hsC ho hx₀
      simp only [C₀C, πs_apply_apply, hx₀', hx₀, LocallyConstant.piecewise'_apply_left,
        LocallyConstant.coe_comap, ContinuousMap.coe_mk, Function.comp_apply]
    · have hx₁' : (ProjRestrict C (ord I · < o) ⟨x, hx⟩).val ∈ π (C1 C ho) (ord I · < o) := by
        simpa only [ProjRestrict, Set.MapsTo.val_restrict_apply] using! ⟨x, hx₁, rfl⟩
      simp only [C₁C, πs_apply_apply, LocallyConstant.coe_comap,
        Function.comp_apply, hx₁', LocallyConstant.piecewise'_apply_right]
      congr
      simp only [ContinuousMap.coe_mk, Subtype.mk.injEq]
      exact C1_projOrd C hsC ho hx₁

variable (o) in
/-
**Profinite.NobelingProof.succ_mono** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobelin
gProof`。
形式化陈述：succ_mono : CategoryTheory.Mono (ModuleCat.ofHom (πs C o))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModuleCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inj
ective f
· 使用定理 `Profinite.NobelingProof.injective_πs`：injective_πs (o : Ordinal) : Funct
ion.Injective (πs C o)
-/
theorem succ_mono : CategoryTheory.Mono (ModuleCat.ofHom (πs C o)) := by
  rw [ModuleCat.mono_iff_injective]
  exact injective_πs _ _

include hC in
/-
**Profinite.NobelingProof.succ_exact** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.Nobeli
ngProof`。
形式化陈述：succ_exact : (ShortComplex.mk (ModuleCat.ofHom (πs C o)) (ModuleCat.ofHom 
(Linear_CC' C hsC ho)) (by ext : 2; apply CC_comp_zero)).Exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ShortComplex.moduleCat_exact_iff`：moduleCat_exact_iff : S
.Exact ↔ forall (x₂ : S.X₂) (_ : S.g x₂ = 0), exists (x₁ : S.X₁), S.f x₁ = x₂
· 使用定理 `Profinite.NobelingProof.CC_exact`：CC_exact {f : LocallyConstant C Int} (
hf : Linear_CC' C hsC ho f = 0) : exists y, πs C o y = f
-/
theorem succ_exact :
    (ShortComplex.mk (ModuleCat.ofHom (πs C o)) (ModuleCat.ofHom (Linear_CC' C hsC ho))
    (by ext : 2; apply CC_comp_zero)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro f
  exact CC_exact C hC hsC ho

end ExactSequence

namespace GoodProducts

/--
The `GoodProducts` in `C` that contain `o` (they necessarily start with `o`, see
`GoodProducts.head!_eq_o_of_maxProducts`)
-/
/-
**Profinite.NobelingProof.GoodProducts.MaxProducts** 是 Mathlib 中的一个定义，位于命名空间 `Pr
ofinite.NobelingProof.GoodProducts`。
形式化陈述：MaxProducts : Set (Products I)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2

--- 原说明 ---
The `GoodProducts` in `C` that contain `o` (they necessarily start with `o`, see
`GoodProducts.head!_eq_o_of_maxProducts`)
-/
def MaxProducts : Set (Products I) := {l | l.isGood C ∧ term I ho ∈ l.val}

include hsC in
/-
**Profinite.NobelingProof.GoodProducts.union_succ** 是 Mathlib 中的一个定理，位于命名空间 `Pro
finite.NobelingProof.GoodProducts`。
形式化陈述：union_succ : GoodProducts C = GoodProducts (π C (ord I · < o)) union MaxPr
oducts C ho
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Profinite.NobelingProof.Products.prop_of_isGood_of_contained`：∀ {I : Typ
e u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I]   {l
 : Profinite.NobelingProof.Products I} (o : Ordina…
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Profinite.NobelingProof.ord_term`：ord_term {o : Ordinal} (ho : o < Ordin
al.type ((· < ·) : I -> I -> Prop)) (i : I) : ord I i = o ↔ term I ho = i
· 使用定理 `Profinite.NobelingProof.Products.eval_πs_image`：eval_πs_image {l : Produ
cts I} {o : Ordinal} (hl : forall i in l.val, ord I i < o) : eval C '' { m | m <
 l } = (πs C o) '' eval (π C (ord I …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.Products.eval_πs`：eval_πs {l : Products I} {o : 
Ordinal} (hlt : forall i in l.val, ord I i < o) : πs C o (l.eval (π C (ord I · <
 o))) = l.eval C
· 使用定理 `Submodule.apply_mem_span_image_iff_mem_span`：apply_mem_span_image_iff_me
m_span [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {x : M} {s : Set M} (hf : Fu
nction.Injective f) : f x in Subm…
· 使用定理 `Profinite.NobelingProof.injective_πs`：injective_πs (o : Ordinal) : Funct
ion.Injective (πs C o)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Profinite.NobelingProof.Products.isGood_mono`：isGood_mono {l : Products 
I} {o₁ o₂ : Ordinal} (h : o₁ <= o₂) (hl : l.isGood (π C (ord I · < o₁))) : l.isG
ood (π C (ord I · < o₂))
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Order.lt_succ`：lt_succ (a : α) : a < succ a
· 使用定理 `Profinite.NobelingProof.contained_eq_proj`：contained_eq_proj (o : Ordina
l) (h : contained C o) : C = π C (ord I · < o)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem union_succ : GoodProducts C = GoodProducts (π C (ord I · < o)) ∪ MaxProducts C ho := by
  ext l
  simp only [GoodProducts, MaxProducts, Set.mem_union, Set.mem_ofPred_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases hh : term I ho ∈ l.val
    · exact Or.inr ⟨h, hh⟩
    · left
      intro he
      apply h
      have h' := Products.prop_of_isGood_of_contained C _ h hsC
      simp only [Order.lt_succ_iff] at h'
      have hh' : ∀ a ∈ l.val, ord I a < o := by
        intro a ha
        refine (h' a ha).lt_of_ne ?_
        rw [ne_eq, ord_term ho a]
        rintro rfl
        contradiction
      rwa [Products.eval_πs_image C hh', ← Products.eval_πs C hh',
        Submodule.apply_mem_span_image_iff_mem_span (injective_πs _ _)]
  · refine h.elim (fun hh ↦ ?_) And.left
    have := Products.isGood_mono C (Order.lt_succ o).le hh
    rwa [contained_eq_proj C (Order.succ o) hsC]

/-- The inclusion map from the sum of `GoodProducts (π C (ord I · < o))` and
`(MaxProducts C ho)` to `Products I`. -/
/-
**Profinite.NobelingProof.GoodProducts.sum_to** 是 Mathlib 中的一个定义，位于命名空间 `Profini
te.NobelingProof.GoodProducts`。
形式化陈述：sum_to : (GoodProducts (π C (ord I · < o))) oplus (MaxProducts C ho) -> Pr
oducts I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2

--- 原说明 ---
The inclusion map from the sum of `GoodProducts (π C (ord I · < o))` and
`(MaxProducts C ho)` to `Products I`.
-/
def sum_to : (GoodProducts (π C (ord I · < o))) ⊕ (MaxProducts C ho) → Products I :=
  Sum.elim Subtype.val Subtype.val
/-
**Profinite.NobelingProof.GoodProducts.injective_sum_to** 是 Mathlib 中的一个定理，位于命名空
间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：injective_sum_to : Function.Injective (sum_to C ho)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Function.Injective.sumElim`：∀ {α : Type u} {β : Type v} {γ : Sort u_3} {
f : α → γ} {g : β → γ},   Function.Injective f → Function.Injective g → (∀ (a : 
α) (b : β), f a …
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Profinite.NobelingProof.Products.prop_of_isGood`：prop_of_isGood {l : Pro
ducts I} (J : I -> Prop) [forall j, Decidable (J j)] (h : l.isGood (π C J)) : fo
rall a, a in l.val -> J a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Profinite.NobelingProof.ord_term_aux`：ord_term_aux {o : Ordinal} (ho : o
 < Ordinal.type ((· < ·) : I -> I -> Prop)) : ord I (term I ho) = o
-/
theorem injective_sum_to : Function.Injective (sum_to C ho) := by
  refine Function.Injective.sumElim Subtype.val_injective Subtype.val_injective
    (fun ⟨a,ha⟩ ⟨b,hb⟩ ↦ (fun (hab : a = b) ↦ ?_))
  rw [← hab] at hb
  have ha' := Products.prop_of_isGood C _ ha (term I ho) hb.2
  simp only [ord_term_aux, lt_self_iff_false] at ha'
/-
**Profinite.NobelingProof.GoodProducts.sum_to_range** 是 Mathlib 中的一个定理，位于命名空间 `P
rofinite.NobelingProof.GoodProducts`。
形式化陈述：sum_to_range : Set.range (sum_to C ho) = GoodProducts (π C (ord I · < o)) 
union MaxProducts C ho
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Set.Sum.elim_range`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : 
α → γ) (g : β → γ),   Set.range (Sum.elim f g) = Set.range f ∪ Set.range g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_to_range :
    Set.range (sum_to C ho) = GoodProducts (π C (ord I · < o)) ∪ MaxProducts C ho := by
  have : Set.range (sum_to C ho) = _ ∪ _ := Set.Sum.elim_range _ _
  simp_all

/-- The equivalence from the sum of `GoodProducts (π C (ord I · < o))` and
`(MaxProducts C ho)` to `GoodProducts C`. -/
noncomputable
/-
**Profinite.NobelingProof.GoodProducts.sum_equiv** 是 Mathlib 中的一个定义，位于命名空间 `Prof
inite.NobelingProof.GoodProducts`。
形式化陈述：sum_equiv (hsC : contained C (Order.succ o)) (ho : o < Ordinal.type (· < ·
 : I -> I -> Prop)) : GoodProducts (π C (ord I · < o)) oplus (MaxProducts C ho) 
≃ GoodProducts C
参数：hsC : contained C (Order.succ o)；ho : o < Ordinal.type (· < · : I -> I -> Pro
p)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Profinite.NobelingProof.GoodProducts.injective_sum_to`：injective_sum_to 
: Function.Injective (sum_to C ho)
-/
def sum_equiv (hsC : contained C (Order.succ o)) (ho : o < Ordinal.type (· < · : I → I → Prop)) :
    GoodProducts (π C (ord I · < o)) ⊕ (MaxProducts C ho) ≃ GoodProducts C :=
  calc _ ≃ Set.range (sum_to C ho) := Equiv.ofInjective (sum_to C ho) (injective_sum_to C ho)
       _ ≃ _ := Equiv.setCongr <| by rw [sum_to_range C ho, union_succ C hsC ho]
/-
**Profinite.NobelingProof.GoodProducts.sum_equiv_comp_eval_eq_elim** 是 Mathlib 中
的一个定理，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：sum_equiv_comp_eval_eq_elim : eval C ∘ (sum_equiv C hsC ho).toFun = (Sum.e
lim (fun (l : GoodProducts (π C (ord I · < o))) => Products.eval C l.1) (fun (l 
: MaxProducts C ho) => Products.eval C l.1))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
-/
theorem sum_equiv_comp_eval_eq_elim : eval C ∘ (sum_equiv C hsC ho).toFun =
    (Sum.elim (fun (l : GoodProducts (π C (ord I · < o))) ↦ Products.eval C l.1)
    (fun (l : MaxProducts C ho) ↦ Products.eval C l.1)) := by
  ext ⟨_, _⟩ <;> [rfl; rfl]

/-- Let

`N := LocallyConstant (π C (ord I · < o)) ℤ`

`M := LocallyConstant C ℤ`

`P := LocallyConstant (C' C ho) ℤ`

`ι := GoodProducts (π C (ord I · < o))`

`ι' := GoodProducts (C' C ho')`

`v : ι → N := GoodProducts.eval (π C (ord I · < o))`

Then `SumEval C ho` is the map `u` in the diagram below. It is linearly independent if and only if
`GoodProducts.eval C` is, see `linearIndependent_iff_sum`. The top row is the exact sequence given
by `succ_exact` and `succ_mono`. The left square commutes by `GoodProducts.square_commutes`.
```
0 --→ N --→ M --→  P
      ↑     ↑      ↑
     v|    u|      |
      ι → ι ⊕ ι' ← ι'
```
-/
/-
**Profinite.NobelingProof.GoodProducts.SumEval** 是 Mathlib 中的一个定义，位于命名空间 `Profin
ite.NobelingProof.GoodProducts`。
形式化陈述：SumEval : GoodProducts (π C (ord I · < o)) oplus MaxProducts C ho -> Local
lyConstant C Int
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2

--- 原说明 ---
Let

`N := LocallyConstant (π C (ord I · < o)) ℤ`

`M := LocallyConstant C ℤ`

`P := LocallyConstant (C' C ho) ℤ`

`ι := GoodProducts (π C (ord I · < o))`

`ι' := GoodProducts (C' C ho')`

`v : ι → N := GoodProducts.eval (π C (ord I · < o))`

Then `SumEval C ho` is the map `u` in the diagram below. It is linearly independ
ent if and only if
`GoodProducts.eval C` is, see `linearIndependent_iff_sum`. The top row is the ex
act sequence given
by `succ_exact` and `succ_mono`. The left square commutes by `GoodProducts.squar
e_commutes`.
```
0 --→ N --→ M --→  P
      ↑     ↑      ↑
     v|    u|      |
      ι → ι ⊕ ι' ← ι'
```
-/
def SumEval : GoodProducts (π C (ord I · < o)) ⊕ MaxProducts C ho →
    LocallyConstant C ℤ :=
  Sum.elim (fun l ↦ l.1.eval C) (fun l ↦ l.1.eval C)

set_option backward.isDefEq.respectTransparency false in
include hsC in
/-
**Profinite.NobelingProof.GoodProducts.linearIndependent_iff_sum** 是 Mathlib 中的一
个定理，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：linearIndependent_iff_sum : LinearIndependent Int (eval C) ↔ LinearIndepen
dent Int (SumEval C ho)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
· 使用定理 `Profinite.NobelingProof.GoodProducts.SumEval.eq_1`：∀ {I : Type u} (C : S
et (I → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u
}}   (ho : o < Ordinal.type fun x1 x2 =…
· 使用定理 `Profinite.NobelingProof.GoodProducts.sum_equiv_comp_eval_eq_elim`：sum_eq
uiv_comp_eval_eq_elim : eval C ∘ (sum_equiv C hsC ho).toFun = (Sum.elim (fun (l 
: GoodProducts (π C (ord I · < o))) => Products.eval C…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem linearIndependent_iff_sum :
    LinearIndependent ℤ (eval C) ↔ LinearIndependent ℤ (SumEval C ho) := by
  rw [← linearIndependent_equiv (sum_equiv C hsC ho), SumEval,
    ← sum_equiv_comp_eval_eq_elim C hsC ho]
  exact Iff.rfl

set_option backward.isDefEq.respectTransparency false in
include hsC in
/-
**Profinite.NobelingProof.GoodProducts.span_sum** 是 Mathlib 中的一个定理，位于命名空间 `Profi
nite.NobelingProof.GoodProducts`。
形式化陈述：span_sum : Set.range (eval C) = Set.range (Sum.elim (fun (l : GoodProducts
 (π C (ord I · < o))) => Products.eval C l.1) (fun (l : MaxProducts C ho) => Pro
ducts.eval C l.1))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.GoodProducts.sum_equiv_comp_eval_eq_elim`：sum_eq
uiv_comp_eval_eq_elim : eval C ∘ (sum_equiv C hsC ho).toFun = (Sum.elim (fun (l 
: GoodProducts (π C (ord I · < o))) => Products.eval C…
· 使用定理 `Equiv.toFun_as_coe`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), e.toFun = ⇑
e
· 使用定理 `EquivLike.range_comp`：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [i
nst : EquivLike E ι ι'] {α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e
) = Set.ra…
-/
theorem span_sum : Set.range (eval C) = Set.range (Sum.elim
    (fun (l : GoodProducts (π C (ord I · < o))) ↦ Products.eval C l.1)
    (fun (l : MaxProducts C ho) ↦ Products.eval C l.1)) := by
  rw [← sum_equiv_comp_eval_eq_elim C hsC ho, Equiv.toFun_as_coe,
    EquivLike.range_comp (e := sum_equiv C hsC ho)]


set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.NobelingProof.GoodProducts.square_commutes** 是 Mathlib 中的一个定理，位于命名空间
 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：square_commutes : SumEval C ho ∘ Sum.inl = ModuleCat.ofHom (πs C o) ∘ eval
 (π C (ord I · < o))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.Products.eval_πs`：eval_πs {l : Products I} {o : 
Ordinal} (hlt : forall i in l.val, ord I i < o) : πs C o (l.eval (π C (ord I · <
 o))) = l.eval C
· 使用定理 `Profinite.NobelingProof.Products.prop_of_isGood`：prop_of_isGood {l : Pro
ducts I} (J : I -> Prop) [forall j, Decidable (J j)] (h : l.isGood (π C J)) : fo
rall a, a in l.val -> J a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Profinite.NobelingProof.πs_apply_apply`：∀ {I : Type u} (C : Set (I → Boo
l)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] (o : Ordinal.{u})   (g : L
ocallyConstant ↑(Profinite.N…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem square_commutes : SumEval C ho ∘ Sum.inl =
    ModuleCat.ofHom (πs C o) ∘ eval (π C (ord I · < o)) := by
  ext l
  dsimp [SumEval]
  rw [← Products.eval_πs C (Products.prop_of_isGood _ _ l.prop)]
  simp [eval]

end GoodProducts

/-
**Profinite.NobelingProof.swapTrue_eq_true** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.
NobelingProof`。
形式化陈述：swapTrue_eq_true (x : I -> Bool) : SwapTrue o x (term I ho) = true
参数：x : I -> Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Profinite.NobelingProof.ord_term_aux`：ord_term_aux {o : Ordinal} (ho : o
 < Ordinal.type ((· < ·) : I -> I -> Prop)) : ord I (term I ho) = o
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem swapTrue_eq_true (x : I → Bool) : SwapTrue o x (term I ho) = true := by
  simp only [SwapTrue, ord_term_aux, ite_true]
/-
**Profinite.NobelingProof.mem_C'_eq_false** 是 Mathlib 中的一个定理，位于命名空间 `Profinite.N
obelingProof`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellF
oundedLT I] {o : Ordinal.{u}}   (ho : o < Ordinal.type fun x1 x2 => x1 < x2),   
∀ x ∈ Profinite.NobelingProof.C' C ho, x (Profinite.NobelingProof.term I ho) = f
alse
参数：C : Set (I → Bool)；ho : o < Ordinal.type fun x1 x2 => x1 < x2；Profinite.Nobel
ingProof.term I ho。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Profinite.NobelingProof.ord_term_aux`：ord_term_aux {o : Ordinal} (ho : o
 < Ordinal.type ((· < ·) : I -> I -> Prop)) : ord I (term I ho) = o
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mem_C'_eq_false : ∀ x, x ∈ C' C ho → x (term I ho) = false := by
  rintro x ⟨_, y, _, rfl⟩
  simp only [Proj, ord_term_aux, lt_self_iff_false, ite_false]

/-- `List.tail` as a `Products`. -/
/-
**Profinite.NobelingProof.Products.Tail** 是 Mathlib 中的一个定义，位于命名空间 `Profinite.Nob
elingProof.Products`。
形式化陈述：{I : Type u} → [inst : LinearOrder I] → Profinite.NobelingProof.Products I
 → Profinite.NobelingProof.Products I
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`List.tail` as a `Products`.
-/
def Products.Tail (l : Products I) : Products I :=
  ⟨l.val.tail, List.IsChain.tail l.prop⟩
/-
**Profinite.NobelingProof.Products.max_eq_o_cons_tail** 是 Mathlib 中的一个定理，位于命名空间 
`Profinite.NobelingProof.Products`。
形式化陈述：∀ {I : Type u} [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordi
nal.{u}}   (ho : o < Ordinal.type fun x1 x2 => x1 < x2) [inst_2 : Inhabited I] (
l : Profinite.NobelingProof.Products I),   ↑l ≠ [] → (↑l).head! = Profinite.Nobe
lingProof.term I ho → ↑l = Profinite.NobelingProof.term I ho :: ↑l.Tail
参数：ho : o < Ordinal.type fun x1 x2 => x1 < x2；l : Profinite.NobelingProof.Produc
ts I；↑l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.cons_head!_tail`：∀ {α : Type u} [inst : Inhabited α] {l : List α}, 
l ≠ [] → l.head! :: l.tail = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Products.max_eq_o_cons_tail [Inhabited I] (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) : l.val = term I ho :: l.Tail.val := by
  rw [← List.cons_head!_tail hl, hlh]
  simp [Tail]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.NobelingProof.Products.max_eq_o_cons_tail'** 是 Mathlib 中的一个定理，位于命名空间
 `Profinite.NobelingProof.Products`。
形式化陈述：∀ {I : Type u} [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordi
nal.{u}}   (ho : o < Ordinal.type fun x1 x2 => x1 < x2) [inst_2 : Inhabited I] (
l : Profinite.NobelingProof.Products I),   ↑l ≠ [] →     (↑l).head! = Profinite.
NobelingProof.term I ho →       ∀ (hlc : List.IsChain (fun x1 x2 => x1 > x2) (Pr
ofinite.NobelingProof.term I ho :: ↑l.Tail)),         l = ⟨Profinite.NobelingPro
of.term I ho :: ↑l.Tail, hlc⟩
参数：ho : o < Ordinal.type fun x1 x2 => x1 < x2；l : Profinite.NobelingProof.Produc
ts I；↑l；hlc : List.IsChain (fun x1 x2 => x1 > x2) (Profinite.NobelingProof.term 
I ho :: ↑l.Tail)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.Products.max_eq_o_cons_tail`：∀ {I : Type u} [ins
t : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (ho : o < Ordi
nal.type fun x1 x2 => x1 < x2) [inst_2 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Products.max_eq_o_cons_tail' [Inhabited I] (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) (hlc : List.IsChain (· > ·) (term I ho :: l.Tail.val)) :
    l = ⟨term I ho :: l.Tail.val, hlc⟩ := by
  simp_rw [← max_eq_o_cons_tail ho l hl hlh, Subtype.coe_eta]

include hsC in
/-
**Profinite.NobelingProof.GoodProducts.head** 是 Mathlib 中的一个定理，位于命名空间 `Profinite
.NobelingProof`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GoodProducts.head!_eq_o_of_maxProducts [Inhabited I] (l : ↑(MaxProducts C ho)) :
    l.val.val.head! = term I ho := by
  rw [eq_comm, ← ord_term ho]
  have hm := l.prop.2
  have := Products.prop_of_isGood_of_contained C _ l.prop.1 hsC l.val.val.head!
    (List.head!_mem_self (List.ne_nil_of_mem hm))
  simp only [Order.lt_succ_iff] at this
  refine eq_of_le_of_not_lt this (not_lt.mpr ?_)
  have h : ord I (term I ho) ≤ ord I l.val.val.head! := by
    simp only [ord, Ordinal.typein_le_typein, not_lt]
    exact Products.rel_head!_of_mem hm
  rwa [ord_term_aux] at h

include hsC in
/-
**Profinite.NobelingProof.GoodProducts.max_eq_o_cons_tail** 是 Mathlib 中的一个定理，位于命
名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellF
oundedLT I] {o : Ordinal.{u}},   Profinite.NobelingProof.contained C (Order.succ
 o) →     ∀ (ho : o < Ordinal.type fun x1 x2 => x1 < x2) (l : ↑(Profinite.Nobeli
ngProof.GoodProducts.MaxProducts C ho)),       ↑↑l = Profinite.NobelingProof.ter
m I ho :: ↑(↑l).Tail
参数：C : Set (I → Bool)；Order.succ o；ho : o < Ordinal.type fun x1 x2 => x1 < x2；l 
: ↑(Profinite.NobelingProof.GoodProducts.MaxProducts C ho)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Profinite.NobelingProof.Products.max_eq_o_cons_tail`：∀ {I : Type u} [ins
t : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (ho : o < Ordi
nal.type fun x1 x2 => x1 < x2) [inst_2 : …
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Profinite.NobelingProof.GoodProducts.head!_eq_o_of_maxProducts`：∀ {I : T
ype u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o
 : Ordinal.{u}},   Profinite.NobelingProof.contained…
-/
theorem GoodProducts.max_eq_o_cons_tail (l : MaxProducts C ho) :
    l.val.val = (term I ho) :: l.val.Tail.val :=
  have : Inhabited I := ⟨term I ho⟩
  Products.max_eq_o_cons_tail ho l.val (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.NobelingProof.Products.evalCons** 是 Mathlib 中的一个定理，位于命名空间 `Profinite
.NobelingProof.Products`。
形式化陈述：∀ {I : Type u_1} [inst : LinearOrder I] {C : Set (I → Bool)} {l : List I} 
{a : I}   (hla : List.IsChain (fun x1 x2 => x1 > x2) (a :: l)),   Profinite.Nobe
lingProof.Products.eval C ⟨a :: l, hla⟩ =     Profinite.NobelingProof.e C a * Pr
ofinite.NobelingProof.Products.eval C ⟨l, ⋯⟩
参数：I → Bool；hla : List.IsChain (fun x1 x2 => x1 > x2) (a :: l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.IsChain.sublist`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List 
α} [Trans R R R],   List.IsChain R l₂ → l₁.Sublist l₂ → List.IsChain R l₁
· 使用定理 `List.tail_sublist`：∀ {α : Type u_1} (l : List α), l.tail.Sublist l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.Products.eval.eq_1`：∀ {I : Type u} (C : Set (I →
 Bool)) [inst : LinearOrder I] (l : Profinite.NobelingProof.Products I),   Profi
nite.NobelingProof.Products.eval…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Products.evalCons {I} [LinearOrder I] {C : Set (I → Bool)} {l : List I} {a : I}
    (hla : (a::l).IsChain (· > ·)) : Products.eval C ⟨a::l,hla⟩ =
    (e C a) * Products.eval C ⟨l,List.IsChain.sublist hla (List.tail_sublist (a::l))⟩ := by
  simp only [eval.eq_1, List.map, List.prod_cons]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Profinite.NobelingProof.Products.max_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Profin
ite.NobelingProof.Products`。
形式化陈述：∀ {I : Type u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellF
oundedLT I] {o : Ordinal.{u}}   (hsC : Profinite.NobelingProof.contained C (Orde
r.succ o)) (ho : o < Ordinal.type fun x1 x2 => x1 < x2)   [inst_2 : Inhabited I]
 (l : Profinite.NobelingProof.Products I),   ↑l ≠ [] →     (↑l).head! = Profinit
e.NobelingProof.term I ho →       (Profinite.NobelingProof.Linear_CC' C hsC ho) 
(Profinite.NobelingProof.Products.eval C l) =         Profinite.NobelingProof.Pr
oducts.eval (Profinite.NobelingProof.C' C ho) l.Tail
参数：C : Set (I → Bool)；hsC : Profinite.NobelingProof.contained C (Order.succ o)；h
o : o < Ordinal.type fun x1 x2 => x1 < x2；l : Profinite.NobelingProof.Products I
；↑l；Profinite.NobelingProof.Linear_CC' C hsC ho；Profinite.NobelingProof.Products
.eval C l；Profinite.NobelingProof.C' C ho。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.Products.max_eq_o_cons_tail`：∀ {I : Type u} [ins
t : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (ho : o < Ordi
nal.type fun x1 x2 => x1 < x2) [inst_2 : …
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Profinite.NobelingProof.Products.max_eq_o_cons_tail'`：∀ {I : Type u} [in
st : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (ho : o < Ord
inal.type fun x1 x2 => x1 < x2) [inst_2 : …
· 使用定理 `List.IsChain.sublist`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List 
α} [Trans R R R],   List.IsChain R l₂ → l₁.Sublist l₂ → List.IsChain R l₁
· 使用定理 `List.tail_sublist`：∀ {α : Type u_1} (l : List α), l.tail.Sublist l
· 使用定理 `Profinite.NobelingProof.Products.evalCons`：∀ {I : Type u_1} [inst : Line
arOrder I] {C : Set (I → Bool)} {l : List I} {a : I}   (hla : List.IsChain (fun 
x1 x2 => x1 > x2) (a :: l)),   …
· 使用定理 `LocallyConstant.ext`：ext ⦃f g : LocallyConstant X Y⦄ (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Profinite.NobelingProof.continuous_CC'₁`：∀ {I : Type u} (C : Set (I → Bo
ol)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (hsC 
: Profinite.NobelingProof.con…
· 使用定理 `Profinite.NobelingProof.continuous_CC'₀`：∀ {I : Type u} (C : Set (I → Bo
ol)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (ho :
 o < Ordinal.type fun x1 x2 =…
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Profinite.NobelingProof.CC'₁.eq_1`：∀ {I : Type u} (C : Set (I → Bool)) [
inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (hsC : Prof
inite.NobelingProof.con…
· 使用定理 `Profinite.NobelingProof.CC'₀.eq_1`：∀ {I : Type u} (C : Set (I → Bool)) [
inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (ho : o < O
rdinal.type fun x1 x2 =…
· 使用定理 `Profinite.NobelingProof.Products.eval_eq`：eval_eq (l : Products I) (x : 
C) : l.eval C x = if forall i, i in l.val -> (x.val i = true) then 1 else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Profinite.NobelingProof.ord_term`：ord_term {o : Ordinal} (ho : o < Ordin
al.type ((· < ·) : I -> I -> Prop)) (i : I) : ord I i = o ↔ term I ho = i
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `List.IsChain.rel_cons`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} 
{a b : α} [Trans R R R], List.IsChain R (a :: l) → b ∈ l → R a b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Profinite.NobelingProof.swapTrue_eq_true`：swapTrue_eq_true (x : I -> Boo
l) : SwapTrue o x (term I ho) = true
（共 39 条，此处仅展示前 30 条）
-/
theorem Products.max_eq_eval [Inhabited I] (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) :
    Linear_CC' C hsC ho (l.eval C) = l.Tail.eval (C' C ho) := by
  have hlc : ((term I ho) :: l.Tail.val).IsChain (· > ·) := by
    rw [← max_eq_o_cons_tail ho l hl hlh]; exact l.prop
  rw [max_eq_o_cons_tail' ho l hl hlh hlc, Products.evalCons]
  ext x
  simp only [Linear_CC', Linear_CC'₁, LocallyConstant.comapₗ, Linear_CC'₀, Subtype.coe_eta,
    LinearMap.sub_apply, LinearMap.coe_mk, AddHom.coe_mk, LocallyConstant.sub_apply,
    LocallyConstant.coe_comap, LocallyConstant.coe_mul, ContinuousMap.coe_mk, Function.comp_apply,
    Pi.mul_apply]
  rw [CC'₁, CC'₀, Products.eval_eq, Products.eval_eq, Products.eval_eq]
  simp only [mul_ite, mul_one, mul_zero]
  have hi' : ∀ i, i ∈ l.Tail.val → (x.val i = SwapTrue o x.val i) := by
    intro i hi
    simp only [SwapTrue, @eq_comm _ (x.val i), ite_eq_right_iff, ord_term ho]
    rintro rfl
    exact ((List.IsChain.rel_cons hlc hi).ne rfl).elim
  have H : (∀ i, i ∈ l.Tail.val → (x.val i = true)) =
      (∀ i, i ∈ l.Tail.val → (SwapTrue o x.val i = true)) := by
    apply forall_congr; intro i; apply forall_congr; intro hi; rw [hi' i hi]
  simp only [H]
  split_ifs with h₁ h₂ h₃ <;> try (dsimp [e])
  · rw [if_pos (swapTrue_eq_true _ _), if_neg]
    · rfl
    · simp [mem_C'_eq_false C ho x x.prop]
  · push Not at h₂; obtain ⟨i, hi⟩ := h₂; exfalso; rw [hi' i hi.1] at hi; exact hi.2 (h₁ i hi.1)
  · push Not at h₁; obtain ⟨i, hi⟩ := h₁; exfalso; rw [← hi' i hi.1] at hi; exact hi.2 (h₃ i hi.1)

namespace GoodProducts

/-
**Profinite.NobelingProof.GoodProducts.max_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `Pr
ofinite.NobelingProof.GoodProducts`。
形式化陈述：max_eq_eval (l : MaxProducts C ho) : Linear_CC' C hsC ho (l.val.eval C) = 
l.val.Tail.eval (C' C ho)
参数：l : MaxProducts C ho。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Profinite.NobelingProof.Products.max_eq_eval`：∀ {I : Type u} (C : Set (I
 → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   
(hsC : Profinite.NobelingProof.con…
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Profinite.NobelingProof.GoodProducts.head!_eq_o_of_maxProducts`：∀ {I : T
ype u} (C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o
 : Ordinal.{u}},   Profinite.NobelingProof.contained…
-/
theorem max_eq_eval (l : MaxProducts C ho) :
    Linear_CC' C hsC ho (l.val.eval C) = l.val.Tail.eval (C' C ho) :=
  have : Inhabited I := ⟨term I ho⟩
  Products.max_eq_eval _ _ _ _ (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)
/-
**Profinite.NobelingProof.GoodProducts.max_eq_eval_unapply** 是 Mathlib 中的一个定理，位于
命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：max_eq_eval_unapply : (Linear_CC' C hsC ho) ∘ (fun (l : MaxProducts C ho) 
=> Products.eval C l.val) = (fun l => l.val.Tail.eval (C' C ho))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Profinite.NobelingProof.GoodProducts.max_eq_eval`：max_eq_eval (l : MaxPr
oducts C ho) : Linear_CC' C hsC ho (l.val.eval C) = l.val.Tail.eval (C' C ho)
-/
theorem max_eq_eval_unapply :
    (Linear_CC' C hsC ho) ∘ (fun (l : MaxProducts C ho) ↦ Products.eval C l.val) =
    (fun l ↦ l.val.Tail.eval (C' C ho)) := by
  ext1 l
  exact max_eq_eval _ _ _ _

include hsC in
/-
**Profinite.NobelingProof.GoodProducts.isChain_cons_of_lt** 是 Mathlib 中的一个定理，位于命
名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：isChain_cons_of_lt (l : MaxProducts C ho) (q : Products I) (hq : q < l.val
.Tail) : List.IsChain (fun x x_1 => x > x_1) (term I ho :: q.val)
参数：l : MaxProducts C ho；q : Products I；hq : q < l.val.Tail。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.isChain_iff_pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α} [Trans R R R], List.IsChain R l ↔ List.Pairwise R l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Profinite.NobelingProof.Products.rel_head!_of_mem`：∀ {I : Type u} [inst 
: LinearOrder I] [inst_1 : Inhabited I] {i : I} {l : Profinite.NobelingProof.Pro
ducts I},   i ∈ ↑l → i ≤ (↑l).head!
· 使用定理 `Profinite.NobelingProof.Products.head!_le_of_lt`：∀ {I : Type u} [inst : 
LinearOrder I] [inst_1 : Inhabited I] {q l : Profinite.NobelingProof.Products I}
,   q < l → ↑q ≠ [] → (↑q).head! ≤ (↑…
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `Profinite.NobelingProof.Products.lt_iff_lex_lt`：lt_iff_lex_lt (l m : Pro
ducts I) : l < m ↔ List.Lex (· < ·) l.val m.val
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `List.rel_of_pairwise_cons`：∀ {α : Type u_1} {a : α} {l : List α} {R : α 
→ α → Prop}, List.Pairwise R (a :: l) → ∀ {a' : α}, a' ∈ l → R a a'
· 使用定理 `Profinite.NobelingProof.GoodProducts.max_eq_o_cons_tail`：∀ {I : Type u} 
(C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordi
nal.{u}},   Profinite.NobelingProof.contained…
· 使用定理 `List.head!_mem_self`：∀ {α : Type u} [inst : Inhabited α] {l : List α}, l
 ≠ [] → l.head! ∈ l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem isChain_cons_of_lt (l : MaxProducts C ho)
    (q : Products I) (hq : q < l.val.Tail) :
    List.IsChain (fun x x_1 ↦ x > x_1) (term I ho :: q.val) := by
  have : Inhabited I := ⟨term I ho⟩
  rw [List.isChain_iff_pairwise]
  simp only [gt_iff_lt, List.pairwise_cons]
  refine ⟨fun a ha ↦ lt_of_le_of_lt (Products.rel_head!_of_mem ha) ?_,
    List.isChain_iff_pairwise.mp q.prop⟩
  refine lt_of_le_of_lt (Products.head!_le_of_lt hq (q.val.ne_nil_of_mem ha)) ?_
  by_cases hM : l.val.Tail.val = []
  · rw [Products.lt_iff_lex_lt, hM] at hq
    simp only [List.not_lex_nil] at hq
  · have := l.val.prop
    rw [max_eq_o_cons_tail C hsC ho l, List.isChain_iff_pairwise] at this
    exact List.rel_of_pairwise_cons this (List.head!_mem_self hM)

include hsC in
/-
**Profinite.NobelingProof.GoodProducts.good_lt_maxProducts** 是 Mathlib 中的一个定理，位于
命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：good_lt_maxProducts (q : GoodProducts (π C (ord I · < o))) (l : MaxProduct
s C ho) : List.Lex (· < ·) q.val.val l.val.val
参数：q : GoodProducts (π C (ord I · < o))；l : MaxProducts C ho。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.GoodProducts.max_eq_o_cons_tail`：∀ {I : Type u} 
(C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordi
nal.{u}},   Profinite.NobelingProof.contained…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.cons_head!_tail`：∀ {α : Type u} [inst : Inhabited α] {l : List α}, 
l ≠ [] → l.head! :: l.tail = l
· 使用定理 `Ordinal.typein_lt_typein`：typein_lt_typein (r : α -> α -> Prop) [IsWellO
rder α r] {a b : α} : typein r a < typein r b ↔ r a b
· 使用定理 `Ordinal.typein_enum`：typein_enum (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : typein r (enum r ⟨o, h⟩) = o
· 使用定理 `Profinite.NobelingProof.Products.prop_of_isGood`：prop_of_isGood {l : Pro
ducts I} (J : I -> Prop) [forall j, Decidable (J j)] (h : l.isGood (π C J)) : fo
rall a, a in l.val -> J a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `List.head!_mem_self`：∀ {α : Type u} [inst : Inhabited α] {l : List α}, l
 ≠ [] → l.head! ∈ l
-/
theorem good_lt_maxProducts (q : GoodProducts (π C (ord I · < o)))
    (l : MaxProducts C ho) : List.Lex (· < ·) q.val.val l.val.val := by
  have : Inhabited I := ⟨term I ho⟩
  by_cases h : q.val.val = []
  · rw [h, max_eq_o_cons_tail C hsC ho l]
    exact List.Lex.nil
  · rw [← List.cons_head!_tail h, max_eq_o_cons_tail C hsC ho l]
    apply List.Lex.rel
    rw [← Ordinal.typein_lt_typein (· < ·)]
    simp only [term, Ordinal.typein_enum]
    exact Products.prop_of_isGood C _ q.prop q.val.val.head! (List.head!_mem_self h)

set_option backward.isDefEq.respectTransparency.types false in
include hC hsC in
/--
Removing the leading `o` from a term of `MaxProducts C` yields a list which `isGood` with respect to
`C'`.
-/
/-
**Profinite.NobelingProof.GoodProducts.maxTail_isGood** 是 Mathlib 中的一个定理，位于命名空间 
`Profinite.NobelingProof.GoodProducts`。
形式化陈述：maxTail_isGood (l : MaxProducts C ho) (h₁ : ⊤ <= Submodule.span Int (Set.r
ange (eval (π C (ord I · < o))))) : l.val.Tail.isGood (C' C ho)
参数：l : MaxProducts C ho；h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord 
I · < o))))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Profinite.NobelingProof.GoodProducts.max_eq_eval`：max_eq_eval (l : MaxPr
oducts C ho) : Linear_CC' C hsC ho (l.val.eval C) = l.val.Tail.eval (C' C ho)
· 使用定理 `Finsupp.mem_span_image_iff_linearCombination`：mem_span_image_iff_linearC
ombination {s : Set α} {x : M} : x in span R (v '' s) ↔ exists l in supported R 
R s, linearCombination R v l = x
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finsupp.sum_congr`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst
 : Zero M] [inst_1 : AddCommMonoid N] {f : α →₀ M}   {g1 g2 : α → M → N}, (∀ x ∈
 f.supp…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Finsupp.mem_supported`：mem_supported {s : Set α} (p : α ->₀ M) : p in su
pported M R s ↔ ↑p.support subseteq s
· 使用定理 `Profinite.NobelingProof.GoodProducts.isChain_cons_of_lt`：isChain_cons_of
_lt (l : MaxProducts C ho) (q : Products I) (hq : q < l.val.Tail) : List.IsChain
 (fun x x_1 => x > x_1) (term I ho :: q.val)
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Profinite.NobelingProof.Products.max_eq_eval`：∀ {I : Type u} (C : Set (I
 → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   
(hsC : Profinite.NobelingProof.con…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Profinite.NobelingProof.Products.max_eq_o_cons_tail`：∀ {I : Type u} [ins
t : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordinal.{u}}   (ho : o < Ordi
nal.type fun x1 x2 => x1 < x2) [inst_2 : …
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.prod_cons`：∀ {α : Type u} [inst : Mul α] [inst_1 : One α] {a : α} {
l : List α}, (a :: l).prod = a * l.prod
· 使用定理 `Profinite.NobelingProof.succ_exact`：succ_exact : (ShortComplex.mk (Modul
eCat.ofHom (πs C o)) (ModuleCat.ofHom (Linear_CC' C hsC ho)) (by ext : 2; apply 
CC_comp_zero)).Exact
· 使用引理 `CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker`：moduleCat_
exact_iff_range_eq_ker : S.Exact ↔ LinearMap.range S.f.hom = LinearMap.ker S.g.h
om
· 使用定理 `LinearMap.sub_mem_ker_iff`：sub_mem_ker_iff {x y} : x - y in ker f ↔ f x 
= f y
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Finsupp.mem_span_range_iff_exists_finsupp`：mem_span_range_iff_exists_fin
supp {v : α -> M} {x : M} : x in span R (range v) ↔ exists c : α ->₀ R, (c.sum f
un i a => a • v i) = x
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Removing the leading `o` from a term of `MaxProducts C` yields a list which `isG
ood` with respect to
`C'`.
-/
theorem maxTail_isGood (l : MaxProducts C ho)
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (ord I · < o))))) :
    l.val.Tail.isGood (C' C ho) := by
  have : Inhabited I := ⟨term I ho⟩
  -- Write `l.Tail` as a linear combination of smaller products:
  intro h
  rw [Finsupp.mem_span_image_iff_linearCombination, ← max_eq_eval C hsC ho] at h
  obtain ⟨m, ⟨hmmem, hmsum⟩⟩ := h
  rw [Finsupp.linearCombination_apply] at hmsum
  -- Write the image of `l` under `Linear_CC'` as `Linear_CC'` applied to the linear combination
  -- above, with leading `term I ho`'s added to each term:
  have : (Linear_CC' C hsC ho) (l.val.eval C) = (Linear_CC' C hsC ho)
      (Finsupp.sum m fun i a ↦ a • ((term I ho :: i.1).map (e C)).prod) := by
    rw [← hmsum]
    simp only [map_finsuppSum]
    apply Finsupp.sum_congr
    intro q hq
    rw [map_smul]
    rw [Finsupp.mem_supported] at hmmem
    have hx'' : q < l.val.Tail := hmmem hq
    have : ∃ (p : Products I), p.val ≠ [] ∧ p.val.head! = term I ho ∧ q = p.Tail :=
      ⟨⟨term I ho :: q.val, isChain_cons_of_lt C hsC ho l q hx''⟩,
        ⟨List.cons_ne_nil _ _, by simp only [List.head!_cons],
        by simp only [Products.Tail, List.tail_cons, Subtype.coe_eta]⟩⟩
    obtain ⟨p, hp⟩ := this
    rw [hp.2.2, ← Products.max_eq_eval C hsC ho p hp.1 hp.2.1]
    dsimp [Products.eval]
    rw [Products.max_eq_o_cons_tail ho p hp.1 hp.2.1, List.map_cons, List.prod_cons]
  have hse := succ_exact C hC hsC ho
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hse
  dsimp [ModuleCat.ofHom] at hse
  -- Rewrite `this` using exact sequence manipulations to conclude that a term is in the range of
  -- the linear map `πs`:
  rw [← LinearMap.sub_mem_ker_iff, ← hse] at this
  obtain ⟨(n : LocallyConstant (π C (ord I · < o)) ℤ), hn⟩ := this
  rw [eq_sub_iff_add_eq] at hn
  have hn' := h₁ (Submodule.mem_top : n ∈ ⊤)
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn'
  obtain ⟨w, hc⟩ := hn'
  rw [← hc, map_finsuppSum] at hn
  apply l.prop.1
  rw [← hn]
  -- Now we just need to prove that a sum of two terms belongs to a span:
  apply Submodule.add_mem
  · apply Submodule.finsuppSum_mem
    intro q _
    rw [map_smul]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    dsimp only [eval]
    rw [Products.eval_πs C (Products.prop_of_isGood _ _ q.prop)]
    refine ⟨q.val, ⟨?_, rfl⟩⟩
    simp only [Products.lt_iff_lex_lt, Set.mem_ofPred_eq]
    exact good_lt_maxProducts C hsC ho q l
  · apply Submodule.finsuppSum_mem
    intro q hq
    apply Submodule.smul_mem
    apply Submodule.subset_span
    rw [Finsupp.mem_supported] at hmmem
    rw [← Finsupp.mem_support_iff] at hq
    refine ⟨⟨term I ho :: q.val, isChain_cons_of_lt C hsC ho l q (hmmem hq)⟩, ⟨?_, rfl⟩⟩
    simp only [Products.lt_iff_lex_lt, Set.mem_ofPred_eq]
    rw [max_eq_o_cons_tail C hsC ho l]
    exact List.Lex.cons ((Products.lt_iff_lex_lt q l.val.Tail).mp (hmmem hq))

/-- Given `l : MaxProducts C ho`, its `Tail` is a `GoodProducts (C' C ho)`. -/
noncomputable
/-
**Profinite.NobelingProof.GoodProducts.MaxToGood** 是 Mathlib 中的一个定义，位于命名空间 `Prof
inite.NobelingProof.GoodProducts`。
形式化陈述：MaxToGood (h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord I · < o
))))) : MaxProducts C ho -> GoodProducts (C' C ho)
参数：h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord I · < o))))。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Profinite.NobelingProof.GoodProducts.maxTail_isGood`：maxTail_isGood (l :
 MaxProducts C ho) (h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord I · 
< o))))) : l.val.Tail.isGood (C' C ho)
-/
def MaxToGood
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (ord I · < o))))) :
    MaxProducts C ho → GoodProducts (C' C ho) :=
  fun l ↦ ⟨l.val.Tail, maxTail_isGood C hC hsC ho l h₁⟩
/-
**Profinite.NobelingProof.GoodProducts.maxToGood_injective** 是 Mathlib 中的一个定理，位于
命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：maxToGood_injective (h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (o
rd I · < o))))) : (MaxToGood C hC hsC ho h₁).Injective
参数：h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord I · < o))))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.GoodProducts.max_eq_o_cons_tail`：∀ {I : Type u} 
(C : Set (I → Bool)) [inst : LinearOrder I] [inst_1 : WellFoundedLT I] {o : Ordi
nal.{u}},   Profinite.NobelingProof.contained…
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem maxToGood_injective
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (ord I · < o))))) :
    (MaxToGood C hC hsC ho h₁).Injective := by
  intro m n h
  apply Subtype.ext ∘ Subtype.ext
  rw [Subtype.ext_iff] at h
  dsimp [MaxToGood] at h
  rw [max_eq_o_cons_tail C hsC ho m, max_eq_o_cons_tail C hsC ho n, h]

include hC in
/-
**Profinite.NobelingProof.GoodProducts.linearIndependent_comp_of_eval** 是 Mathli
b 中的一个定理，位于命名空间 `Profinite.NobelingProof.GoodProducts`。
形式化陈述：linearIndependent_comp_of_eval (h₁ : ⊤ <= Submodule.span Int (Set.range (e
val (π C (ord I · < o))))) : LinearIndependent Int (eval (C' C ho)) -> LinearInd
ependent Int (ModuleCat.ofHom (Linear_CC' C hsC ho) ∘ SumEval C ho ∘ Sum.inr)
参数：h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord I · < o))))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Profinite.NobelingProof.GoodProducts.max_eq_eval_unapply`：max_eq_eval_un
apply : (Linear_CC' C hsC ho) ∘ (fun (l : MaxProducts C ho) => Products.eval C l
.val) = (fun l => l.val.Tail.eval (C' C ho))
· 使用定理 `Profinite.NobelingProof.GoodProducts.maxToGood_injective`：maxToGood_inje
ctive (h₁ : ⊤ <= Submodule.span Int (Set.range (eval (π C (ord I · < o))))) : (M
axToGood C hC hsC ho h₁).Injective
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
-/
theorem linearIndependent_comp_of_eval
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (ord I · < o))))) :
    LinearIndependent ℤ (eval (C' C ho)) →
    LinearIndependent ℤ (ModuleCat.ofHom (Linear_CC' C hsC ho) ∘ SumEval C ho ∘ Sum.inr) := by
  dsimp [SumEval, ModuleCat.ofHom]
  rw [max_eq_eval_unapply C hsC ho]
  intro h
  let f := MaxToGood C hC hsC ho h₁
  have hf : f.Injective := maxToGood_injective C hC hsC ho h₁
  have hh : (fun l ↦ Products.eval (C' C ho) l.val.Tail) = eval (C' C ho) ∘ f := rfl
  rw [hh]
  exact h.comp f hf

end GoodProducts

end Profinite.NobelingProof

