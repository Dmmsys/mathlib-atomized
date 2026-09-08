/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
public import Mathlib.Data.Finite.Sigma

/-!
# Existence of a rank function to natural numbers

In this file, we show that if `P : A.Pairing` is
a regular pairing of subcomplex `A` of a simplicial set `X`,
then there exists a rank function for `P` with values in `ℕ`.

-/

@[expose] public section

universe u

open Simplicial

namespace SSet.Subcomplex

variable {X : SSet.{u}} {A : X.Subcomplex}

namespace Pairing

variable (P : A.Pairing)

/-
**SSet.Subcomplex.Pairing.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (y : P.II) : Finite { x // P.AncestralRel x y } := by
  let T := { x : P.II // P.AncestralRel x y }
  let U := Σ (d : Fin (P.p y).1.dim), ⦋d⦌ ⟶ ⦋(P.p y).1.1.1.1⦌
  let ψ : U → X.S := fun ⟨d, f⟩ ↦ S.mk (X.map f.op (P.p y).1.simplex)
  have h (t : T) : ∃ u, ψ u = t.1.1.toS := by
    obtain ⟨f, _, hf⟩ := N.le_iff_exists_mono.1 t.2.2.le
    refine ⟨⟨⟨t.1.1.dim, ?_⟩, f⟩, ?_⟩
    · simpa using SSet.N.dim_lt_of_lt t.2.2
    · rwa [SSet.S.ext_iff]
  choose φ hφ using h
  apply Finite.of_injective φ
  intro t₁ t₂ h
  rw [Subtype.ext_iff, Subtype.ext_iff, N.ext_iff, SSet.N.ext_iff, ← hφ, ← hφ, h]

section

variable {y : P.II} (hy : Acc P.AncestralRel y)

/-- Auxiliary definition for `SSet.Subcomplex.Pairing.Rank`. -/
/-
**SSet.Subcomplex.Pairing.rank'** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.Pairi
ng`。
形式化陈述：rank' : Nat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `SSet.Subcomplex.Pairing.Rank`.
-/
noncomputable def rank' : ℕ :=
  Acc.recOn hy (fun y _ r ↦ ⨆ (x : { x // P.AncestralRel x y }), r x x.2 + 1)
/-
**SSet.Subcomplex.Pairing.rank'_eq** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Subcomplex.Pa
iring`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} (P : A.Pairing) {y : ↑P.II} (hy : A
cc P.AncestralRel y),   P.rank' hy = ⨆ x, P.rank' ⋯ + 1
参数：P : A.Pairing；hy : Acc P.AncestralRel y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Acc.inv`：∀ {α : Sort u} {r : α → α → Prop} {x y : α}, Acc r x → r y x → 
Acc r y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma rank'_eq :
    P.rank' hy = ⨆ (x : { x // P.AncestralRel x y }), P.rank' (hy.inv x.2) + 1 := by
  change P.rank' (Acc.intro y fun _ => hy.inv) = _
  rfl
/-
**SSet.Subcomplex.Pairing.rank'_lt** 是 Mathlib 中的一个定理，位于命名空间 `SSet.Subcomplex.Pa
iring`。
形式化陈述：∀ {X : _root_.SSet} {A : X.Subcomplex} (P : A.Pairing) {y : ↑P.II} (hy : A
cc P.AncestralRel y) {x : ↑P.II}   (r : P.AncestralRel x y), P.rank' ⋯ < P.rank'
 hy
参数：P : A.Pairing；hy : Acc P.AncestralRel y；r : P.AncestralRel x y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Acc.inv`：∀ {α : Sort u} {r : α → α → Prop} {x y : α}, Acc r x → r y x → 
Acc r y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SSet.Subcomplex.Pairing.rank'_eq`：∀ {X : _root_.SSet} {A : X.Subcomplex}
 (P : A.Pairing) {y : ↑P.II} (hy : Acc P.AncestralRel y),   P.rank' hy = ⨆ x, P.
rank' ⋯ + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_one_le_iff`：∀ {n m : ℕ}, n + 1 ≤ m ↔ n < m
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Finite.bddAbove_range`：Finite.bddAbove_range [IsDirectedOrder α] (f : ι 
-> α) : BddAbove (Set.range f)
· 使用定理 `SSet.Subcomplex.Pairing.instFiniteSubtypeElemNIIAncestralRel`：∀ {X : _ro
ot_.SSet} {A : X.Subcomplex} (P : A.Pairing) (y : ↑P.II), Finite { x // P.Ancest
ralRel x y }
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
-/
lemma rank'_lt {x : P.II} (r : P.AncestralRel x y) :
    P.rank' (hy.inv r) < P.rank' hy := by
  rw [P.rank'_eq hy, ← Nat.add_one_le_iff]
  exact le_csSup (Finite.bddAbove_range _) ⟨⟨x, r⟩, rfl⟩

end

section IsRegular

variable [P.IsRegular]

/-- The rank function with values in `ℕ` relative to the well founded
ancestrality relation of a regular pairing. -/
/-
**SSet.Subcomplex.Pairing.rank** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomplex.Pairin
g`。
形式化陈述：rank (x : P.II) : Nat
参数：x : P.II。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rank function with values in `ℕ` relative to the well founded
ancestrality relation of a regular pairing.
-/
noncomputable def rank (x : P.II) : ℕ :=
  P.rank' (P.wf.apply x)

variable {P} in
/-
**SSet.Subcomplex.Pairing.rank_lt** 是 Mathlib 中的一个引理，位于命名空间 `SSet.Subcomplex.Pai
ring`。
形式化陈述：rank_lt {x y : P.II} (h : P.AncestralRel x y) : P.rank x < P.rank y
参数：h : P.AncestralRel x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.Pairing.rank'_lt`：∀ {X : _root_.SSet} {A : X.Subcomplex}
 (P : A.Pairing) {y : ↑P.II} (hy : Acc P.AncestralRel y) {x : ↑P.II}   (r : P.An
cestralRel x y), P.ran…
-/
lemma rank_lt {x y : P.II} (h : P.AncestralRel x y) :
    P.rank x < P.rank y :=
  P.rank'_lt _ h

/-- The canonical rank function with values in `ℕ` of a regular pairing. -/
/-
**SSet.Subcomplex.Pairing.rankFunction** 是 Mathlib 中的一个定义，位于命名空间 `SSet.Subcomple
x.Pairing`。
形式化陈述：rankFunction : P.RankFunction Nat where rank
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SSet.Subcomplex.Pairing.rank_lt`：rank_lt {x y : P.II} (h : P.AncestralRe
l x y) : P.rank x < P.rank y

--- 原说明 ---
The canonical rank function with values in `ℕ` of a regular pairing.
-/
noncomputable def rankFunction : P.RankFunction ℕ where
  rank := P.rank
  lt := P.rank_lt
/-
**SSet.Subcomplex.Pairing.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (P.RankFunction ℕ) := ⟨P.rankFunction⟩
/-
**SSet.Subcomplex.Pairing.** 是 Mathlib 中的一个实例，位于命名空间 `SSet.Subcomplex.Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (P.WeakRankFunction ℕ) := ⟨P.rankFunction.toWeakRankFunction⟩

end IsRegular

/-
**SSet.Subcomplex.Pairing.isRegular_iff_nonempty_rankFunction** 是 Mathlib 中的一个引理
，位于命名空间 `SSet.Subcomplex.Pairing`。
形式化陈述：isRegular_iff_nonempty_rankFunction [P.IsProper] : P.IsRegular ↔ Nonempty 
(P.RankFunction Nat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.Pairing.instNonemptyRankFunctionNat`：∀ {X : _root_.SSet}
 {A : X.Subcomplex} (P : A.Pairing) [P.IsRegular], Nonempty (P.RankFunction ℕ)
· 使用引理 `SSet.Subcomplex.Pairing.RankFunction.isRegular`：isRegular [P.IsProper] :
 P.IsRegular where wf
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
-/
lemma isRegular_iff_nonempty_rankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.RankFunction ℕ) :=
  ⟨fun _ ↦ inferInstance, fun ⟨h⟩ ↦ h.isRegular⟩
/-
**SSet.Subcomplex.Pairing.isRegular_iff_nonempty_weakRankFunction** 是 Mathlib 中的
一个引理，位于命名空间 `SSet.Subcomplex.Pairing`。
形式化陈述：isRegular_iff_nonempty_weakRankFunction [P.IsProper] : P.IsRegular ↔ Nonem
pty (P.WeakRankFunction Nat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SSet.Subcomplex.Pairing.instNonemptyWeakRankFunctionNat`：∀ {X : _root_.S
Set} {A : X.Subcomplex} (P : A.Pairing) [P.IsRegular], Nonempty (P.WeakRankFunct
ion ℕ)
· 使用引理 `SSet.Subcomplex.Pairing.WeakRankFunction.isRegular`：isRegular : P.IsRegu
lar where wf
· 使用定理 `instWellFoundedLTNat`：WellFoundedLT ℕ
-/
lemma isRegular_iff_nonempty_weakRankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.WeakRankFunction ℕ) :=
  ⟨fun _ ↦ inferInstance, fun ⟨h⟩ ↦ h.isRegular⟩

end Pairing

namespace PairingCore

variable (P : A.PairingCore)

/-
**SSet.Subcomplex.PairingCore.isRegular_iff_nonempty_rankFunction** 是 Mathlib 中的
一个引理，位于命名空间 `SSet.Subcomplex.PairingCore`。
形式化陈述：isRegular_iff_nonempty_rankFunction [P.IsProper] : P.IsRegular ↔ Nonempty 
(P.RankFunction Nat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.PairingCore.isRegular_pairing_iff`：isRegular_pairing_iff
 (h : A.PairingCore) : h.pairing.IsRegular ↔ h.IsRegular
· 使用引理 `SSet.Subcomplex.Pairing.isRegular_iff_nonempty_rankFunction`：isRegular_i
ff_nonempty_rankFunction [P.IsProper] : P.IsRegular ↔ Nonempty (P.RankFunction N
at)
· 使用定理 `SSet.Subcomplex.PairingCore.instIsProperPairingOfIsProper`：∀ {X : _root_
.SSet} {A : X.Subcomplex} (h : A.PairingCore) [h.IsProper], h.pairing.IsProper
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma isRegular_iff_nonempty_rankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.RankFunction ℕ) := by
  rw [← isRegular_pairing_iff, Pairing.isRegular_iff_nonempty_rankFunction]
  exact (P.rankFunctionEquiv ℕ).symm.nonempty_congr
/-
**SSet.Subcomplex.PairingCore.isRegular_iff_nonempty_weakRankFunction** 是 Mathli
b 中的一个引理，位于命名空间 `SSet.Subcomplex.PairingCore`。
形式化陈述：isRegular_iff_nonempty_weakRankFunction [P.IsProper] : P.IsRegular ↔ Nonem
pty (P.WeakRankFunction Nat)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SSet.Subcomplex.PairingCore.isRegular_pairing_iff`：isRegular_pairing_iff
 (h : A.PairingCore) : h.pairing.IsRegular ↔ h.IsRegular
· 使用引理 `SSet.Subcomplex.Pairing.isRegular_iff_nonempty_weakRankFunction`：isRegul
ar_iff_nonempty_weakRankFunction [P.IsProper] : P.IsRegular ↔ Nonempty (P.WeakRa
nkFunction Nat)
· 使用定理 `SSet.Subcomplex.PairingCore.instIsProperPairingOfIsProper`：∀ {X : _root_
.SSet} {A : X.Subcomplex} (h : A.PairingCore) [h.IsProper], h.pairing.IsProper
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma isRegular_iff_nonempty_weakRankFunction [P.IsProper] :
    P.IsRegular ↔ Nonempty (P.WeakRankFunction ℕ) := by
  rw [← isRegular_pairing_iff, Pairing.isRegular_iff_nonempty_weakRankFunction]
  exact (P.weakRankFunctionEquiv ℕ).symm.nonempty_congr

end PairingCore

end SSet.Subcomplex

