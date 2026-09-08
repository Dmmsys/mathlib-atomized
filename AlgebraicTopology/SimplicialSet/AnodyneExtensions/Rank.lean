/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PairingCore
public import Mathlib.Order.OrderIsoNat

/-!
# Rank functions for pairings

We introduce types of (weak) rank functions for a pairing `P`
of a subcomplex `A` of a simplicial set `X`. These are
functions `f : P.II → α` such that `P.AncestralRel x y` implies `f x < f y`
(in the weak case, we require this only under the additional condition
that `x` and `y` are of the same dimension). Such rank functions
are used in order to show that the ancestrality relation on `P.II` is well founded,
i.e. that `P` is regular (when we already know `P` is proper).
Conversely, we shall show that if `P` is regular,
then `P.RankFunction ℕ` is non empty (TODO @joelriou).

(We also introduce similar definitions for the structure `PairingCore`.)


## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe v u

open CategoryTheory Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} {A : X.Subcomplex}

namespace Pairing

variable {X : SSet.{u}} {A : X.Subcomplex} (P : A.Pairing)
  (α : Type v) [PartialOrder α]

/-- A rank function for a pairing is a function from the type (II) simplices
to a partially ordered type which maps ancestrality relations to strict inequalities. -/
/-
**SSet.Subcomplex.Pairing.RankFunction** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Subcomp
lex.Pairing`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → A.Pairing → (α : Type v) → [Parti
alOrder α] → Type (max u v)
参数：α : Type v；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A rank function for a pairing is a function from the type (II) simplices
to a partially ordered type which maps ancestrality relations to strict inequali
ties.
-/
structure RankFunction where
  /-- the rank function -/
  rank : P.II → α
  lt {x y : P.II} : P.AncestralRel x y → rank x < rank y

namespace RankFunction

variable {P α} [WellFoundedLT α] (f : P.RankFunction α)

include f

/-
**SSet.Subcomplex.Pairing.RankFunction.wf_ancestralRel** 是 Mathlib 中的一个引理，位于命名空间
 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：wf_ancestralRel : WellFounded P.AncestralRel
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wellFounded_iff_isEmpty_descending_chain`：wellFounded_iff_isEmpty_descen
ding_chain {α} {r : α -> α -> Prop} : WellFounded r ↔ IsEmpty { f : Nat -> α // 
forall n, r (f (n + 1)) (f n) …
· 使用定理 `not_strictAnti_of_wellFoundedLT`：not_strictAnti_of_wellFoundedLT [Preord
er α] [WellFoundedLT α] (f : Nat -> α) : ¬ StrictAnti f
· 使用定理 `strictAnti_nat_of_succ_lt`：strictAnti_nat_of_succ_lt {f : Nat -> α} (hf 
: forall n, f (n + 1) < f n) : StrictAnti f
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.lt`：∀ {X : _root_.SSet} {A : X.Subc
omplex} {P : A.Pairing} {α : Type v} [inst : PartialOrder α] (self : P.RankFunct
ion α)   {x y : ↑P.II}, P.Anc…
-/
lemma wf_ancestralRel : WellFounded P.AncestralRel := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  exact ⟨fun ⟨g, hg⟩ ↦ not_strictAnti_of_wellFoundedLT (f.rank ∘ g)
    (strictAnti_nat_of_succ_lt (fun n ↦ f.lt (hg n)))⟩
/-
**SSet.Subcomplex.Pairing.RankFunction.isRegular** 是 Mathlib 中的一个引理，位于命名空间 `SSet
.Subcomplex.Pairing.RankFunction`。
形式化陈述：isRegular [P.IsProper] : P.IsRegular where wf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.wf_ancestralRel`：wf_ancestralRel : 
WellFounded P.AncestralRel
-/
lemma isRegular [P.IsProper] : P.IsRegular where
  wf := f.wf_ancestralRel

end RankFunction

/-- A weak rank function for a pairing is a function from the type (II) simplices
to a partially ordered type which maps an ancestrality relation between
simplices of the same dimension to a strict inequality. -/
/-
**SSet.Subcomplex.Pairing.WeakRankFunction** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Sub
complex.Pairing`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → A.Pairing → (α : Type v) → [Parti
alOrder α] → Type (max u v)
参数：α : Type v；max u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weak rank function for a pairing is a function from the type (II) simplices
to a partially ordered type which maps an ancestrality relation between
simplices of the same dimension to a strict inequality.
-/
structure WeakRankFunction where
  /-- the (weak) rank function -/
  rank : P.II → α
  lt {x y : P.II} : P.AncestralRel x y → x.1.dim = y.1.dim → rank x < rank y

namespace WeakRankFunction

variable {P α} [WellFoundedLT α] [P.IsProper] (f : P.WeakRankFunction α)

include f

set_option backward.isDefEq.respectTransparency.types false in
/-
**SSet.Subcomplex.Pairing.WeakRankFunction.wf_ancestralRel** 是 Mathlib 中的一个引理，位于
命名空间 `SSet.Subcomplex.Pairing.WeakRankFunction`。
形式化陈述：wf_ancestralRel : WellFounded P.AncestralRel
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `wellFounded_iff_isEmpty_descending_chain`：wellFounded_iff_isEmpty_descen
ding_chain {α} {r : α -> α -> Prop} : WellFounded r ↔ IsEmpty { f : Nat -> α // 
forall n, r (f (n + 1)) (f n) …
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `SSet.Subcomplex.Pairing.AncestralRel.dim_le`：∀ {X : _root_.SSet} {A : X.
Subcomplex} {P : A.Pairing} [P.IsProper] {x y : ↑P.II},   P.AncestralRel x y → (
↑x).dim ≤ (↑y).dim
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `wellFoundedGT_iff_monotone_chain_condition`：wellFoundedGT_iff_monotone_c
hain_condition [PartialOrder α] : WellFoundedGT α ↔ forall a : Nat ->o α, exists
 n, forall m, n <= m -> a n = a …
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_gt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedGT α],
 IsWellOrder α fun x1 x2 => x2 < x1
· 使用定理 `instWellFoundedGTOrderDualOfWellFoundedLT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedLT α], WellFoundedGT αᵒᵈ
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
· 使用定理 `not_strictAnti_of_wellFoundedLT`：not_strictAnti_of_wellFoundedLT [Preord
er α] [WellFoundedLT α] (f : Nat -> α) : ¬ StrictAnti f
· 使用定理 `strictAnti_nat_of_succ_lt`：strictAnti_nat_of_succ_lt {f : Nat -> α} (hf 
: forall n, f (n + 1) < f n) : StrictAnti f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `SSet.Subcomplex.Pairing.WeakRankFunction.lt`：∀ {X : _root_.SSet} {A : X.
Subcomplex} {P : A.Pairing} {α : Type v} [inst : PartialOrder α]   (self : P.Wea
kRankFunction α) {x y : ↑P.II}, P…
-/
lemma wf_ancestralRel : WellFounded P.AncestralRel := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  refine ⟨fun ⟨g, hg⟩ ↦ ?_⟩
  obtain ⟨n₀, hn₀⟩ :=
    (wellFoundedGT_iff_monotone_chain_condition (α := ℕᵒᵈ)).1
      inferInstance ⟨fun n ↦ (g n).1.dim,
        monotone_nat_of_le_succ (fun n ↦ (hg n).dim_le)⟩
  dsimp at hn₀
  refine not_strictAnti_of_wellFoundedLT (fun n ↦ f.rank (g (n₀ + n)))
    (strictAnti_nat_of_succ_lt (fun n ↦ ?_))
  rw [← add_assoc]
  exact f.lt (hg _) (by rw [← hn₀ (n₀ + n + 1) (by lia), ← hn₀ (n₀ + n) (by lia)])
/-
**SSet.Subcomplex.Pairing.WeakRankFunction.isRegular** 是 Mathlib 中的一个引理，位于命名空间 `
SSet.Subcomplex.Pairing.WeakRankFunction`。
形式化陈述：isRegular : P.IsRegular where wf
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.Pairing.WeakRankFunction.wf_ancestralRel`：wf_ancestralRe
l : WellFounded P.AncestralRel
-/
lemma isRegular : P.IsRegular where
  wf := f.wf_ancestralRel

end WeakRankFunction

/-- The weak rank function attached to a rank function. -/
@[simps]
/-
**SSet.Subcomplex.Pairing.RankFunction.toWeakRankFunction** 是 Mathlib 中的一个定义，位于命
名空间 `SSet.Subcomplex.Pairing.RankFunction`。
形式化陈述：{X : _root_.SSet} →   {A : X.Subcomplex} →     (P : A.Pairing) → (α : Type
 v) → [inst : PartialOrder α] → P.RankFunction α → P.WeakRankFunction α
参数：P : A.Pairing；α : Type v。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.Pairing.RankFunction.lt`：∀ {X : _root_.SSet} {A : X.Subc
omplex} {P : A.Pairing} {α : Type v} [inst : PartialOrder α] (self : P.RankFunct
ion α)   {x y : ↑P.II}, P.Anc…

--- 原说明 ---
The weak rank function attached to a rank function.
-/
def RankFunction.toWeakRankFunction (f : P.RankFunction α) :
    P.WeakRankFunction α where
  rank := f.rank
  lt h _ := f.lt h

end Pairing

namespace PairingCore

variable {X : SSet.{u}} {A : X.Subcomplex} (h : A.PairingCore)
  (α : Type v) [PartialOrder α]

/-- A rank function for `h : A.PairingCore` is a function from the index type `h.ι`
to a partially ordered type which maps the ancestrality relations to strict inequalities. -/
/-
**SSet.Subcomplex.PairingCore.RankFunction** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet.Sub
complex.PairingCore`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → A.PairingCore → (α : Type v) → [P
artialOrder α] → Type (max u_1 v)
参数：α : Type v；max u_1 v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A rank function for `h : A.PairingCore` is a function from the index type `h.ι`
to a partially ordered type which maps the ancestrality relations to strict ineq
ualities.
-/
structure RankFunction where
  /-- the rank function -/
  rank : h.ι → α
  lt {x y : h.ι} : h.AncestralRel x y → rank x < rank y

/-- A weak rank function `h : A.PairingCore` is a function from the index type `h.ι`
to a partially ordered type which maps an ancestrality relation between
indices of the same dimension to a strict inequality. -/
/-
**SSet.Subcomplex.PairingCore.WeakRankFunction** 是 Mathlib 中的一个归纳类型，位于命名空间 `SSet
.Subcomplex.PairingCore`。
形式化陈述：{X : _root_.SSet} → {A : X.Subcomplex} → A.PairingCore → (α : Type v) → [P
artialOrder α] → Type (max u_1 v)
参数：α : Type v；max u_1 v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A weak rank function `h : A.PairingCore` is a function from the index type `h.ι`
to a partially ordered type which maps an ancestrality relation between
indices of the same dimension to a strict inequality.
-/
structure WeakRankFunction where
  /-- the (weak) rank function -/
  rank : h.ι → α
  lt {x y : h.ι} : h.AncestralRel x y → h.dim x = h.dim y → rank x < rank y

set_option backward.isDefEq.respectTransparency.types false in
/-- Rank functions for `h : A.PairingCore` correspond to
rank functions for `h.pairing : A.Pairing`. -/
/-
**SSet.Subcomplex.PairingCore.rankFunctionEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SSet.
Subcomplex.PairingCore`。
形式化陈述：rankFunctionEquiv : h.RankFunction α ≃ h.pairing.RankFunction α where toFu
n f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Rank functions for `h : A.PairingCore` correspond to
rank functions for `h.pairing : A.Pairing`.
-/
noncomputable def rankFunctionEquiv :
    h.RankFunction α ≃ h.pairing.RankFunction α where
  toFun f :=
    { rank s := f.rank (h.equivII.symm s)
      lt {x y} hxy := by
        obtain ⟨x, rfl⟩ := h.equivII.surjective x
        obtain ⟨y, rfl⟩ := h.equivII.surjective y
        rw [← ancestralRel_iff] at hxy
        simpa using f.lt hxy }
  invFun g :=
    { rank x := g.rank (h.equivII x)
      lt hxy := by
        rw [ancestralRel_iff] at hxy
        exact g.lt hxy }
  left_inv _ := by simp
  right_inv _ := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Weak rank functions for `h : A.PairingCore` correspond to
weak rank functions for `h.pairing : A.Pairing`. -/
/-
**SSet.Subcomplex.PairingCore.weakRankFunctionEquiv** 是 Mathlib 中的一个定义，位于命名空间 `S
Set.Subcomplex.PairingCore`。
形式化陈述：weakRankFunctionEquiv : h.WeakRankFunction α ≃ h.pairing.WeakRankFunction 
α where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Weak rank functions for `h : A.PairingCore` correspond to
weak rank functions for `h.pairing : A.Pairing`.
-/
noncomputable def weakRankFunctionEquiv :
    h.WeakRankFunction α ≃ h.pairing.WeakRankFunction α where
  toFun f :=
    { rank s := f.rank (h.equivII.symm s)
      lt {x y} hxy := by
        obtain ⟨x, rfl⟩ := h.equivII.surjective x
        obtain ⟨y, rfl⟩ := h.equivII.surjective y
        rw [← ancestralRel_iff] at hxy
        simpa using f.lt hxy }
  invFun g :=
    { rank x := g.rank (h.equivII x)
      lt hxy := by
        rw [ancestralRel_iff] at hxy
        exact g.lt hxy }
  left_inv _ := by simp
  right_inv _ := by simp

variable {h α} [WellFoundedLT α]
/-
**SSet.Subcomplex.PairingCore.RankFunction.isRegular** 是 Mathlib 中的一个定理，位于命名空间 `
SSet.Subcomplex.PairingCore.RankFunction`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} {h : A.PairingCore} {α : Type v} [i
nst : PartialOrder α] [WellFoundedLT α]   [h.IsProper] (f : h.RankFunction α), h
.IsRegular
参数：f : h.RankFunction α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.PairingCore.isRegular_pairing_iff`：isRegular_pairing_iff
 (h : A.PairingCore) : h.pairing.IsRegular ↔ h.IsRegular
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.isRegular`：isRegular [P.IsProper] :
 P.IsRegular where wf
· 使用定理 `SSet.Subcomplex.PairingCore.instIsProperPairingOfIsProper`：∀ {X : _root_
.SSet} {A : X.Subcomplex} (h : A.PairingCore) [h.IsProper], h.pairing.IsProper
-/
lemma RankFunction.isRegular [h.IsProper] (f : h.RankFunction α) : h.IsRegular := by
  rw [← isRegular_pairing_iff]
  exact (h.rankFunctionEquiv α f).isRegular
/-
**SSet.Subcomplex.PairingCore.WeakRankFunction.isRegular** 是 Mathlib 中的一个定理，位于命名
空间 `SSet.Subcomplex.PairingCore.WeakRankFunction`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} {h : A.PairingCore} {α : Type v} [i
nst : PartialOrder α] [WellFoundedLT α]   [h.IsProper] (f : h.WeakRankFunction α
), h.IsRegular
参数：f : h.WeakRankFunction α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.PairingCore.isRegular_pairing_iff`：isRegular_pairing_iff
 (h : A.PairingCore) : h.pairing.IsRegular ↔ h.IsRegular
· 使用引理 `SSet.Subcomplex.Pairing.WeakRankFunction.isRegular`：isRegular : P.IsRegu
lar where wf
· 使用定理 `SSet.Subcomplex.PairingCore.instIsProperPairingOfIsProper`：∀ {X : _root_
.SSet} {A : X.Subcomplex} (h : A.PairingCore) [h.IsProper], h.pairing.IsProper
-/
lemma WeakRankFunction.isRegular [h.IsProper] (f : h.WeakRankFunction α) : h.IsRegular := by
  rw [← isRegular_pairing_iff]
  exact (h.weakRankFunctionEquiv α f).isRegular

end PairingCore

end SSet.Subcomplex

