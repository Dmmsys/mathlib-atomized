/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Submodule.Order
public import Mathlib.Algebra.Order.Module.Archimedean
public import Mathlib.Algebra.Order.Module.Equiv
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.RingTheory.HahnSeries.Lex

/-!
# Hahn embedding theorem on ordered modules

This file proves a variant of the Hahn embedding theorem:

For a linearly ordered module `M` over an Archimedean division ring `K`,
there exists a strictly monotone linear map to lexicographically ordered
`R⟦FiniteArchimedeanClass M⟧` with an archimedean `K`-module `R`,
as long as there are embeddings from a certain family of Archimedean submodules to `R`.

The family of Archimedean submodules `HahnEmbedding.ArchimedeanStrata K M` is indexed by
`(c : ArchimedeanClass M)`, and each submodule is a complement of `ArchimedeanClass.ball K c`
under `ArchimedeanClass.closedBall K c`. The embeddings from these submodules are specified by
`HahnEmbedding.Seed K M R`.

By setting `K = ℚ` and `R = ℝ`, the condition can be trivially satisfied, leading
to a proof of the classic Hahn embedding theorem. (See `hahnEmbedding_isOrderedAddMonoid`)

## Main theorem

* `hahnEmbedding_isOrderedModule`:
  there exists a strictly monotone `M →ₗ[K] Lex R⟦FiniteArchimedeanClass M⟧` that maps
  `ArchimedeanClass M` to `HahnSeries.orderTop` in the expected way, as long as
  `HahnEmbedding.Seed K M R` is nonempty.

## References

* [M. Hausner, J.G. Wendel, *Ordered vector spaces*][hausnerwendel1952]
-/

@[expose] public section

/-! ### Step 1: base embedding

We start with `HahnEmbedding.ArchimedeanStrata` that gives a family of Archimedean submodules,
and a "seed" `HahnEmbedding.Seed` that specifies how to embed each
`HahnEmbedding.ArchimedeanStrata.stratum` into `R`.

From these, we create a partial map from the direct sum of all `stratum` to `R⟦Γ⟧`.
If `ArchimedeanClass M` is finite, the direct sum is the entire `M` and we are done
(though we don't handle this case separately). Otherwise, we will extend the map to `M` in the
following steps.
-/

open FiniteArchimedeanClass DirectSum HahnSeries

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable [Module K M] [IsOrderedModule K M]
variable {R : Type*} [AddCommGroup R] [LinearOrder R]
variable [Module K R]

namespace HahnEmbedding

variable (K M) in
/-- A family of submodules indexed by `FiniteArchimedeanClass M` that
are complements between `FiniteArchimedeanClass.ball` and `FiniteArchimedeanClass.closedBall`. -/
/-
**HahnEmbedding.ArchimedeanStrata** 是 Mathlib 中的一个归纳类型，位于命名空间 `HahnEmbedding`。
形式化陈述：(K : Type u_1) →   [inst : DivisionRing K] →     [inst_1 : LinearOrder K] 
→       [IsOrderedRing K] →         [Archimedean K] →           (M : Type u_2) →
             [inst_4 : AddCommGroup M] →               [inst_5 : LinearOrder M] 
→                 [IsOrderedAddMonoid M] → [inst_7 : _root_.Module K M] → [IsOrd
eredModule K M] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of submodules indexed by `FiniteArchimedeanClass M` that
are complements between `FiniteArchimedeanClass.ball` and `FiniteArchimedeanClas
s.closedBall`.
-/
structure ArchimedeanStrata where
  /-- For each `FiniteArchimedeanClass`, specify a corresponding submodule. -/
  stratum : FiniteArchimedeanClass M → Submodule K M
  /-- `stratum` and `FiniteArchimedeanClass.ball` are disjoint. -/
  disjoint_ball_stratum (c : FiniteArchimedeanClass M) : Disjoint (ball K c) (stratum c)
  /-- `stratum` and `FiniteArchimedeanClass.ball`
    are codisjoint under `FiniteArchimedeanClass.closedBall`. -/
  ball_sup_stratum_eq (c : FiniteArchimedeanClass M) : ball K c ⊔ stratum c = closedBall K c

namespace ArchimedeanStrata
variable (u : ArchimedeanStrata K M) {c : FiniteArchimedeanClass M}

/-
**HahnEmbedding.ArchimedeanStrata.** 是 Mathlib 中的一个实例，位于命名空间 `HahnEmbedding.Arch
imedeanStrata`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (ArchimedeanStrata K M) := by
  have hstratum (c : FiniteArchimedeanClass M) :
      ∃ G : Submodule K M, Disjoint (ball K c) G ∧ ball K c ⊔ G = closedBall K c :=
    IsModularLattice.exists_disjoint_and_sup_eq (ball_lt_closedBall _).le
  choose g h1 h2 using hstratum
  exact ⟨g, h1, h2⟩
/-
**HahnEmbedding.ArchimedeanStrata.stratum_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `Hahn
Embedding.ArchimedeanStrata`。
形式化陈述：stratum_ne_bot : u.stratum c != ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.not_lt`：∀ {α : Type u_2} [inst : Preorder α] {a b : α}, a = b → ¬a < 
b
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `HahnEmbedding.ArchimedeanStrata.ball_sup_stratum_eq`：∀ {K : Type u_1} [i
nst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_
3 : Archimedean K]   {M : Type u_2} [inst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FiniteArchimedeanClass.ball_lt_closedBall`：ball_lt_closedBall {c : Finit
eArchimedeanClass M} : ball K c < closedBall K c
-/
theorem stratum_ne_bot : u.stratum c ≠ ⊥ :=
  fun eq ↦ (eq ▸ u.ball_sup_stratum_eq c).not_lt <| by simpa using ball_lt_closedBall _
/-
**HahnEmbedding.ArchimedeanStrata.nontrivial_stratum** 是 Mathlib 中的一个实例，位于命名空间 `
HahnEmbedding.ArchimedeanStrata`。
形式化陈述：nontrivial_stratum : Nontrivial (u.stratum c)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot : Nontrivial p ↔ 
p != ⊥
· 使用定理 `HahnEmbedding.ArchimedeanStrata.stratum_ne_bot`：stratum_ne_bot : u.strat
um c != ⊥
-/
instance nontrivial_stratum : Nontrivial (u.stratum c) :=
  (Submodule.nontrivial_iff_ne_bot).mpr (stratum_ne_bot _)
/-
**HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum** 是 Mathlib 
中的一个定理，位于命名空间 `HahnEmbedding.ArchimedeanStrata`。
形式化陈述：archimedeanClassMk_of_mem_stratum {a : M} (ha : a in u.stratum c) (h0 : a 
!= 0) : ArchimedeanClass.mk a = c
参数：ha : a in u.stratum c；h0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `FiniteArchimedeanClass.mem_ball_iff`：mem_ball_iff {a : M} {c : FiniteArc
himedeanClass M} : a in ball K c ↔ forall h : a != 0, c < mk a h
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `HahnEmbedding.ArchimedeanStrata.disjoint_ball_stratum`：∀ {K : Type u_1} 
[inst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [ins
t_3 : Archimedean K]   {M : Type u_2} [inst…
· 使用定理 `FiniteArchimedeanClass.mem_closedBall_iff`：mem_closedBall_iff {a : M} {c
 : FiniteArchimedeanClass M} : a in closedBall K c ↔ forall h : a != 0, c <= mk 
a h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnEmbedding.ArchimedeanStrata.ball_sup_stratum_eq`：∀ {K : Type u_1} [i
nst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_
3 : Archimedean K]   {M : Type u_2} [inst…
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
-/
theorem archimedeanClassMk_of_mem_stratum {a : M}
    (ha : a ∈ u.stratum c) (h0 : a ≠ 0) : ArchimedeanClass.mk a = c := by
  apply le_antisymm
  · contrapose! h0 with hlt
    have ha' : a ∈ ball K c := (mem_ball_iff K).mpr fun _ ↦ hlt
    exact (Submodule.disjoint_def.mp (u.disjoint_ball_stratum _)) _ ha' ha
  · apply (mem_closedBall_iff K).mp _ h0
    rw [← u.ball_sup_stratum_eq c]
    exact Submodule.mem_sup_right ha
/-
**HahnEmbedding.ArchimedeanStrata.archimedean_stratum** 是 Mathlib 中的一个实例，位于命名空间 
`HahnEmbedding.ArchimedeanStrata`。
形式化陈述：archimedean_stratum : Archimedean (u.stratum c)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ArchimedeanClass.archimedean_of_mk_eq_mk`：∀ {M : Type u_1} [inst : AddCo
mmGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M],   (∀ (a : M
), a ≠ 0 → ∀ (b : M), b ≠ 0 → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum`：archi
medeanClassMk_of_mem_stratum {a : M} (ha : a in u.stratum c) (h0 : a != 0) : Arc
himedeanClass.mk a = c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `ArchimedeanClass.mk_eq_mk`：∀ {M : Type u_1} [inst : AddCommGroup M] [ins
t_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M},   ArchimedeanCla
ss.mk a = Archi…
-/
instance archimedean_stratum : Archimedean (u.stratum c) := by
  apply ArchimedeanClass.archimedean_of_mk_eq_mk
  intro a ha b hb
  suffices ArchimedeanClass.mk a.val = ArchimedeanClass.mk b.val by
    rw [ArchimedeanClass.mk_eq_mk] at this ⊢
    exact this
  rw [u.archimedeanClassMk_of_mem_stratum a.prop (by simpa using ha)]
  rw [u.archimedeanClassMk_of_mem_stratum b.prop (by simpa using hb)]
/-
**HahnEmbedding.ArchimedeanStrata.iSupIndep_stratum** 是 Mathlib 中的一个定理，位于命名空间 `H
ahnEmbedding.ArchimedeanStrata`。
形式化陈述：iSupIndep_stratum : iSupIndep u.stratum
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.disjoint_def'`：disjoint_def' {p p' : Submodule R M} : Disjoint
 p p' ↔ forall x in p, forall y in p', x = y -> x = (0 : M)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_iSup_iff_exists_dfinsupp'`：mem_iSup_iff_exists_dfinsupp' (
p : ι -> Submodule R N) [forall (i) (x : p i), Decidable (x != 0)] (x : N) : x i
n iSup p ↔ exists f : Π₀ i, p…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFinsupp.sum.eq_1`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i) →
 Decida…
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum`：archi
medeanClassMk_of_mem_stratum {a : M} (ha : a in u.stratum c) (h0 : a != 0) : Arc
himedeanClass.mk a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `ArchimedeanClass.mk_sum`：∀ {M : Type u_1} [inst : AddCommGroup M] [inst_
1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {ι : Type u_2}   [inst_3 : Li
nearOrder ι] …
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `FiniteArchimedeanClass.val_mk`：∀ {M : Type u_1} [inst : AddCommGroup M] 
[inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a : M} (h : a ≠ 0),   
↑(FiniteArchimedean…
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
（共 31 条，此处仅展示前 30 条）
-/
theorem iSupIndep_stratum : iSupIndep u.stratum := by
  intro c
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ b).mp hb
  obtain hf' := congr(ArchimedeanClass.mk $hf)
  contrapose! hf' with h0
  rw [← hab, DFinsupp.sum]
  by_cases! hnonempty : f.support.Nonempty
  · have hmem (x : FiniteArchimedeanClass M) : (f x).val ∈ u.stratum x :=
      Set.mem_of_mem_of_subset (f x).prop (by simp)
    have hmono : StrictMonoOn (fun i ↦ ArchimedeanClass.mk (f i).val) f.support := by
      intro x hx y hy hxy
      change ArchimedeanClass.mk (f x).val < ArchimedeanClass.mk (f y).val
      rw [u.archimedeanClassMk_of_mem_stratum (hmem x) (by simpa using hx)]
      rw [u.archimedeanClassMk_of_mem_stratum (hmem y) (by simpa using hy)]
      exact hxy
    rw [ArchimedeanClass.mk_sum hnonempty hmono, u.archimedeanClassMk_of_mem_stratum (hmem _)
      (by simpa using f.support.min'_mem hnonempty), ← val_mk h0, Subtype.coe_ne_coe]
    by_contra!
    obtain h := this ▸ Finset.min'_mem f.support hnonempty
    contrapose! h
    have := u.archimedeanClassMk_of_mem_stratum ha h0
    rw [← val_mk h0, ← Subtype.ext_iff] at this
    simpa [DFinsupp.notMem_support_iff, this] using (f c).prop
  · rw [hnonempty]
    symm
    simpa using h0

/-- The minimal submodule that contains all strata.

This is the domain of our "base" embedding into Hahn series, which we will extend into a full
embedding. -/
/-
**HahnEmbedding.ArchimedeanStrata.baseDomain** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbe
dding.ArchimedeanStrata`。
形式化陈述：baseDomain
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimal submodule that contains all strata.

This is the domain of our "base" embedding into Hahn series, which we will exten
d into a full
embedding.
-/
def baseDomain := ⨆ c, u.stratum c

/-- `ArchimedeanStrata.stratum` as a submodule of
`ArchimedeanStrata.baseDomain`. -/
/-
**HahnEmbedding.ArchimedeanStrata.stratum'** 是 Mathlib 中的一个缩写定义，位于命名空间 `HahnEmbe
dding.ArchimedeanStrata`。
形式化陈述：stratum' (c : FiniteArchimedeanClass M) : Submodule K (baseDomain u)
参数：c : FiniteArchimedeanClass M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ArchimedeanStrata.stratum` as a submodule of
`ArchimedeanStrata.baseDomain`.
-/
abbrev stratum' (c : FiniteArchimedeanClass M) : Submodule K (baseDomain u) :=
  (u.stratum c).comap u.baseDomain.subtype
/-
**HahnEmbedding.ArchimedeanStrata.iSupIndep_stratum'** 是 Mathlib 中的一个定理，位于命名空间 `
HahnEmbedding.ArchimedeanStrata`。
形式化陈述：iSupIndep_stratum' : iSupIndep u.stratum'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `iSupIndep_map_orderIso_iff`：iSupIndep_map_orderIso_iff {ι : Sort*} {α β 
: Type*} [CompleteLattice α] [CompleteLattice β] (f : α ≃o β) {a : ι -> α} : iSu
pIndep (f ∘ a) ↔…
· 使用引理 `iSupIndep.of_coe_Iic_comp`：iSupIndep.of_coe_Iic_comp {ι : Sort*} {a : α}
 {t : ι -> Set.Iic a} (ht : iSupIndep ((↑) ∘ t : ι -> α)) : iSupIndep t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `HahnEmbedding.ArchimedeanStrata.iSupIndep_stratum`：iSupIndep_stratum : i
SupIndep u.stratum
-/
theorem iSupIndep_stratum' : iSupIndep u.stratum' := by
  apply (iSupIndep_map_orderIso_iff (Submodule.mapIic u.baseDomain)).mp
  apply iSupIndep.of_coe_Iic_comp
  convert! u.iSupIndep_stratum
  ext1 c
  simpa using! le_iSup _ _
/-
**HahnEmbedding.ArchimedeanStrata.isInternal_stratum'** 是 Mathlib 中的一个定理，位于命名空间 
`HahnEmbedding.ArchimedeanStrata`。
形式化陈述：isInternal_stratum' : DirectSum.IsInternal u.stratum'
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`：isInternal_s
ubmodule_of_iSupIndep_of_iSup_eq_top {A : ι -> Submodule R M} (hi : iSupIndep A)
 (hs : iSup A = ⊤) : IsInternal A
· 使用定理 `HahnEmbedding.ArchimedeanStrata.iSupIndep_stratum'`：iSupIndep_stratum' :
 iSupIndep u.stratum'
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用定理 `iSup_congr`：iSup_congr (h : forall i, f i = g i) : ⨆ i, f i = ⨆ i, g i
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
-/
theorem isInternal_stratum' : DirectSum.IsInternal u.stratum' := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top u.iSupIndep_stratum'
  apply Submodule.map_injective_of_injective u.baseDomain.subtype_injective
  suffices ⨆ i, u.baseDomain ⊓ u.stratum i = u.baseDomain by simpa using! this
  apply iSup_congr
  intro c
  simpa using! le_iSup _ _

noncomputable
/-
**HahnEmbedding.ArchimedeanStrata.** 是 Mathlib 中的一个实例，位于命名空间 `HahnEmbedding.Arch
imedeanStrata`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DirectSum.Decomposition u.stratum' := (u.isInternal_stratum').chooseDecomposition _

end ArchimedeanStrata

variable (K M R) in
/-- `HahnEmbedding.Seed` extends `HahnEmbedding.ArchimedeanStrata` by specifying strictly monotone
linear maps from each `stratum` to module `R`. -/
/-
**HahnEmbedding.Seed** 是 Mathlib 中的一个归纳类型，位于命名空间 `HahnEmbedding`。
形式化陈述：(K : Type u_1) →   [inst : DivisionRing K] →     [inst_1 : LinearOrder K] 
→       [IsOrderedRing K] →         [Archimedean K] →           (M : Type u_2) →
             [inst_4 : AddCommGroup M] →               [inst_5 : LinearOrder M] 
→                 [IsOrderedAddMonoid M] →                   [inst_7 : _root_.Mo
dule K M] →                     [IsOrderedModule K M] →                       (R
 : Type u_3) →                         [inst_9 : AddCommGroup R] → [LinearOrder 
R] → [_root_.Module K R] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HahnEmbedding.Seed` extends `HahnEmbedding.ArchimedeanStrata` by specifying str
ictly monotone
linear maps from each `stratum` to module `R`.
-/
structure Seed extends ArchimedeanStrata K M where
  /-- For each stratum, specify a linear map to `R` as the Hahn series coefficient. -/
  coeff (c : FiniteArchimedeanClass M) : stratum c →ₗ[K] R
  /-- `coeff` is strictly monotone. -/
  strictMono_coeff (c : FiniteArchimedeanClass M) : StrictMono (coeff c)

variable (seed : Seed K M R)

namespace Seed

/-- `HahnEmbedding.Seed.coeff` with `ArchimedeanStrata.stratum'` as domain. -/
/-
**HahnEmbedding.Seed.coeff'** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbedding.Seed`。
形式化陈述：coeff' (c : FiniteArchimedeanClass M) : seed.stratum' c ->ₗ[K] R
参数：c : FiniteArchimedeanClass M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HahnEmbedding.Seed.coeff` with `ArchimedeanStrata.stratum'` as domain.
-/
def coeff' (c : FiniteArchimedeanClass M) : seed.stratum' c →ₗ[K] R :=
  (seed.coeff c).comp (LinearMap.submoduleComap _ _)

/-- Coefficients of Hahn series for each `baseDomain` element. -/
noncomputable
/-
**HahnEmbedding.Seed.hahnCoeff** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbedding.Seed`。
形式化陈述：hahnCoeff : seed.baseDomain ->ₗ[K] (⨁ _ : FiniteArchimedeanClass M, R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def hahnCoeff : seed.baseDomain →ₗ[K] (⨁ _ : FiniteArchimedeanClass M, R) :=
  (DirectSum.lmap seed.coeff') ∘ₗ (DirectSum.decomposeLinearEquiv _).toLinearMap
/-
**HahnEmbedding.Seed.hahnCoeff_apply** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.Se
ed`。
形式化陈述：hahnCoeff_apply {x : seed.baseDomain} {f : Π₀ c, seed.stratum c} (h : x.va
l = f.sum fun c => (seed.stratum c).subtype) (c : FiniteArchimedeanClass M) : se
ed.hahnCoeff x c = seed.coeff c (f c)
参数：h : x.val = f.sum fun c => (seed.stratum c).subtype；c : FiniteArchimedeanClas
s M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.submoduleComap_apply_coe`：∀ {R : Type u_1} {R₂ : Type u_3} {M 
: Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2
 : AddCommMonoid M] [ins…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用定理 `DirectSum.coeAddMonoidHom_eq_dfinsuppSum`：coeAddMonoidHom_eq_dfinsuppSum
 [DecidableEq ι] {M S : Type*} [DecidableEq M] [AddCommMonoid M] [SetLike S M] [
AddSubmonoidClass S M] (A : ι …
· 使用定理 `DFinsupp.sum_mapRange_index`：∀ {ι : Type u} {γ : Type w} [inst : Decidab
leEq ι] {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}   [inst_1 : (i : ι) → Zero (β₁ i)]
 [inst_2 : (i : ι…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_dfinsuppSum`：∀ {ι : Type u} {β : ι → Type v} [inst : DecidableEq ι] 
{R : Type u_1} {S : Type u_2} {H : Type u_3}   [inst_1 : (i : ι) → Zero (β i)] [
inst_…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem hahnCoeff_apply {x : seed.baseDomain} {f : Π₀ c, seed.stratum c}
    (h : x.val = f.sum fun c ↦ (seed.stratum c).subtype) (c : FiniteArchimedeanClass M) :
    seed.hahnCoeff x c = seed.coeff c (f c) := by
  suffices seed.baseDomain.subtype.submoduleComap
      (seed.stratum c) (DirectSum.decompose seed.stratum' x c) = f c by
    simp [Seed.hahnCoeff, coeff', decomposeLinearEquiv_apply, this]
  have hxm {c : FiniteArchimedeanClass M} (x : seed.stratum c) : x.val ∈ seed.baseDomain := by
    apply Set.mem_of_mem_of_subset x.prop
    simpa using! le_iSup _ _
  let f' : ⨁ c, seed.stratum' c :=
    f.mapRange (fun c x ↦ (⟨⟨x.val, hxm x⟩, by simp⟩ : seed.stratum' c)) (by simp)
  have hf : f c = (seed.baseDomain.subtype.submoduleComap (seed.stratum c)) (f' c) := by
    set_option backward.isDefEq.respectTransparency false in
    apply Subtype.ext
    simp [f']
  have hx : x = (decompose seed.stratum').symm f' := by
    change x = f'.coeAddMonoidHom _
    apply Submodule.subtype_injective
    rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum, DFinsupp.sum_mapRange_index (by simp)]
    simp [h]
  simp [hf, hx]

/-- Combining all `HahnEmbedding.Seed.coeff` as
a partial linear map from `HahnEmbedding.Seed.baseDomain` to `HahnSeries`. -/
noncomputable
/-
**HahnEmbedding.Seed.baseEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbedding.Seed
`。
形式化陈述：baseEmbedding : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ where domain
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def baseEmbedding : M →ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ where
  domain := seed.baseDomain
  toFun := (toLexLinearEquiv _ _).toLinearMap ∘ₗ (HahnSeries.ofFinsuppLinearMap _) ∘ₗ
    (finsuppLequivDFinsupp K).symm.toLinearMap ∘ₗ seed.hahnCoeff
/-
**HahnEmbedding.Seed.domain_baseEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbeddi
ng.Seed`。
形式化陈述：domain_baseEmbedding : seed.baseEmbedding.domain = seed.baseDomain
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domain_baseEmbedding : seed.baseEmbedding.domain = seed.baseDomain := rfl
/-
**HahnEmbedding.Seed.coeff_baseEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbeddin
g.Seed`。
形式化陈述：coeff_baseEmbedding {x : seed.baseEmbedding.domain} {f : Π₀ c, seed.stratu
m c} (h : x.val = f.sum fun c => (seed.stratum c).subtype) (c : FiniteArchimedea
nClass M) : (ofLex ((baseEmbedding seed) x)).coeff c = seed.coeff c (f c)
参数：h : x.val = f.sum fun c => (seed.stratum c).subtype；c : FiniteArchimedeanClas
s M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Seed.hahnCoeff_apply`：hahnCoeff_apply {x : seed.baseDomain
} {f : Π₀ c, seed.stratum c} (h : x.val = f.sum fun c => (seed.stratum c).subtyp
e) (c : FiniteArchimedea…
-/
theorem coeff_baseEmbedding {x : seed.baseEmbedding.domain} {f : Π₀ c, seed.stratum c}
    (h : x.val = f.sum fun c ↦ (seed.stratum c).subtype) (c : FiniteArchimedeanClass M) :
    (ofLex ((baseEmbedding seed) x)).coeff c = seed.coeff c (f c) := by
  simpa [baseEmbedding] using! seed.hahnCoeff_apply h c
/-
**HahnEmbedding.Seed.mem_domain_baseEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmb
edding.Seed`。
形式化陈述：mem_domain_baseEmbedding {x : M} {c : FiniteArchimedeanClass M} (h : x in 
seed.stratum c) : x in seed.baseEmbedding.domain
参数：h : x in seed.stratum c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnEmbedding.Seed.domain_baseEmbedding`：domain_baseEmbedding : seed.bas
eEmbedding.domain = seed.baseDomain
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iSup_iff`：le_iSup_iff {s : ι -> α} : a <= iSup s ↔ forall b, (forall 
i, s i <= b) -> a <= b
-/
theorem mem_domain_baseEmbedding {x : M} {c : FiniteArchimedeanClass M} (h : x ∈ seed.stratum c) :
    x ∈ seed.baseEmbedding.domain := by
  apply Set.mem_of_mem_of_subset h
  rw [domain_baseEmbedding]
  simpa using! le_iSup_iff.mpr fun _ h ↦ h c

end Seed

/-! ### Step 2: characterize partial embedding

We characterize the base embedding as a member of a class of partial linear embeddings
`HahnEmbedding.Partial`. These embeddings share nice properties, including being strictly monotone,
transferring `ArchimedeanClass` to `HahnEmbedding.orderTop`, and being "truncation-closed"
(see `HahnEmbedding.IsPartial.truncLT_mem_range`).
-/

/-- A partial linear map is called a "partial Hahn embedding" if it extends
`HahnEmbedding.Seed.baseEmbedding`, is strictly monotone, and is truncation-closed. -/
/-
**HahnEmbedding.IsPartial** 是 Mathlib 中的一个归纳类型，位于命名空间 `HahnEmbedding`。
形式化陈述：{K : Type u_1} →   [inst : DivisionRing K] →     [inst_1 : LinearOrder K] 
→       [inst_2 : IsOrderedRing K] →         [inst_3 : Archimedean K] →         
  {M : Type u_2} →             [inst_4 : AddCommGroup M] →               [inst_5
 : LinearOrder M] →                 [inst_6 : IsOrderedAddMonoid M] →           
        [inst_7 : _root_.Module K M] →                     [inst_8 : IsOrderedMo
dule K M] →                       {R : Type u_3} →                         [inst
_9 : AddCommGroup R] →                           [inst_10 : LinearOrder R] →    
                         [inst_11 : _root_.Module K R] →                        
       HahnEmbedding.Seed K M R → (M →ₗ.[K] Lex (HahnSeries (FiniteArchimedeanCl
ass M) R)) → Prop
参数：M →ₗ.[K] Lex (HahnSeries (FiniteArchimedeanClass M) R)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial linear map is called a "partial Hahn embedding" if it extends
`HahnEmbedding.Seed.baseEmbedding`, is strictly monotone, and is truncation-clos
ed.
-/
structure IsPartial (f : M →ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧) : Prop where
  /-- A partial Hahn embedding is strictly monotone. -/
  strictMono : StrictMono f
  /-- A partial Hahn embedding always extends `baseEmbedding`. -/
  baseEmbedding_le : seed.baseEmbedding ≤ f
  /-- If a Hahn series $f$ is in the range, then any truncation of $f$ is also in the range. -/
  truncLT_mem_range : ∀ x, ∀ c,
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f x))) ∈ LinearMap.range f.toFun

namespace Seed

/-
**HahnEmbedding.Seed.baseEmbedding_pos** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.
Seed`。
形式化陈述：baseEmbedding_pos {x : seed.baseEmbedding.domain} (hx : 0 < x) : 0 < seed.
baseEmbedding x
参数：hx : 0 < x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_iSup_iff_exists_dfinsupp'`：mem_iSup_iff_exists_dfinsupp' (
p : ι -> Submodule R N) [forall (i) (x : p i), Decidable (x != 0)] (x : N) : x i
n iSup p ↔ exists f : Π₀ i, p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `DFinsupp.sum_eq_zero`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst
 : DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i
) → Decida…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `DFinsupp.notMem_support_iff`：notMem_support_iff {f : Π₀ i, β i} {i : ι} 
: i ∉ f.support ↔ f i = 0
· 使用定理 `Finset.eq_empty_iff_forall_notMem`：eq_empty_iff_forall_notMem {s : Finse
t α} : s = ∅ ↔ forall x, x ∉ s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `HahnSeries.lt_iff`：lt_iff (a b : Lex R⟦Γ⟧) : a < b ↔ exists (i : Γ), (fo
rall (j : Γ), j < i -> (ofLex a).coeff j = (ofLex b).coeff j) ∧ (ofLex a).coeff 
i < (of…
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `HahnEmbedding.Seed.coeff_baseEmbedding`：coeff_baseEmbedding {x : seed.ba
seEmbedding.domain} {f : Π₀ c, seed.stratum c} (h : x.val = f.sum fun c => (seed
.stratum c).subtype) (c : Fi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `Subtype.coe_le_coe`：coe_le_coe [LE α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) <= y ↔ x <= y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ArchimedeanClass.pos_of_pos_of_mk_lt`：∀ {M : Type u_1} [inst : AddCommGr
oup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M},   0 <
 a → ArchimedeanClass.mk a…
（共 46 条，此处仅展示前 30 条）
-/
theorem baseEmbedding_pos {x : seed.baseEmbedding.domain} (hx : 0 < x) :
    0 < seed.baseEmbedding x := by
  -- decompose `x` to sum of `stratum`
  have hmem : x.val ∈ seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  have hfpos : 0 < (f.sum fun _ x ↦ x.val) := by
    rw [hf]
    simpa using! hx
  have hsupport : f.support.Nonempty := by
    obtain hne := hfpos.ne.symm
    contrapose! hne with hempty
    apply DFinsupp.sum_eq_zero
    intro c
    simpa using! DFinsupp.notMem_support_iff.mp (Finset.eq_empty_iff_forall_notMem.mp hempty c)
  -- The dictating term for `HahnSeries` < is at the lowest archimedean class of `f.support`
  refine (HahnSeries.lt_iff _ _).mpr ⟨f.support.min' hsupport, ?_, ?_⟩
  · intro j hj
    rw [seed.coeff_baseEmbedding hf.symm]
    rw [DFinsupp.notMem_support_iff.mp ?_]
    · simp
    contrapose! hj
    rw [← Subtype.coe_le_coe, Subtype.coe_mk]
    exact Finset.min'_le f.support _ hj
  -- Show that `f`'s value at dominating archimedean class is positive
  rw [seed.coeff_baseEmbedding hf.symm]
  suffices (seed.coeff (f.support.min' hsupport)) 0 <
      (seed.coeff (f.support.min' hsupport)) (f (f.support.min' hsupport)) by
    simpa using! this
  suffices 0 < (f (f.support.min' hsupport)).val by
    apply (seed.strictMono_coeff (f.support.min' hsupport))
    simpa using! this
  -- using the fact that `f.sum` is positive, we only needs to show that
  -- the remaining terms of f after removing the dominating class is of higher class
  apply ArchimedeanClass.pos_of_pos_of_mk_lt hfpos
  rw [ArchimedeanClass.mk_sub_comm]
  have hferase : (f.sum fun _ x ↦ x.val) - (f (f.support.min' hsupport)).val =
      ∑ x ∈ f.support.erase (f.support.min' hsupport), (f x).val :=
    sub_eq_of_eq_add (Finset.sum_erase_add _ _ (Finset.min'_mem _ hsupport)).symm
  rw [hferase]
  -- Now both sides are `mk (∑ ...)`
  -- We rewrite them to `mk (dominating term)`
  have hmono : StrictMonoOn (fun x ↦ ArchimedeanClass.mk (f x).val) f.support := by
    intro c hc d hd h
    simp only
    rw [seed.archimedeanClassMk_of_mem_stratum (f c).prop (by simpa using! hc)]
    rw [seed.archimedeanClassMk_of_mem_stratum (f d).prop (by simpa using! hd)]
    exact h
  rw [DFinsupp.sum, ArchimedeanClass.mk_sum hsupport hmono]
  rw [seed.archimedeanClassMk_of_mem_stratum (f _).prop
    (by simpa using! f.support.min'_mem hsupport)]
  by_cases! hsupport' : (f.support.erase (f.support.min' hsupport)).Nonempty
  · rw [ArchimedeanClass.mk_sum hsupport' (hmono.mono (by simp))]
    rw [seed.archimedeanClassMk_of_mem_stratum (f _).prop (by
      simpa using! (Finset.mem_erase.mp <| (f.support.erase _).min'_mem hsupport').2)]
    apply Finset.min'_lt_of_mem_erase_min' (α := FiniteArchimedeanClass M)
    apply Finset.min'_mem _ _
  · -- special case: `f` has a single term, and becomes 0 after removing it
    simpa [hsupport'] using! (f.support.min' hsupport).2.lt_top
/-
**HahnEmbedding.Seed.baseEmbedding_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmb
edding.Seed`。
形式化陈述：baseEmbedding_strictMono [IsOrderedAddMonoid R] : StrictMono seed.baseEmbe
dding
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, 0 < a - b → b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `Lex.instIsRightCancelAdd`：∀ {α : Type u_1} [inst : Add α] [IsRightCancel
Add α], IsRightCancelAdd (Lex α)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.map_sub`：map_sub (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x -
 y) = f x - f y
· 使用定理 `HahnEmbedding.Seed.baseEmbedding_pos`：baseEmbedding_pos {x : seed.baseEm
bedding.domain} (hx : 0 < x) : 0 < seed.baseEmbedding x
· 使用定理 `AddMemClass.isRightCancelAdd`：∀ {M : Type u_1} {A : Type u_3} [inst : Ad
d M] [inst_1 : SetLike A M] [hA : AddMemClass A M] [IsRightCancelAdd M]   (S : A
), IsRightCancelAd…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
-/
theorem baseEmbedding_strictMono [IsOrderedAddMonoid R] : StrictMono seed.baseEmbedding := by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  exact baseEmbedding_pos _ <| by simpa using h
/-
**HahnEmbedding.Seed.truncLT_mem_range_baseEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `
HahnEmbedding.Seed`。
形式化陈述：truncLT_mem_range_baseEmbedding (x : seed.baseEmbedding.domain) (c : Finit
eArchimedeanClass M) : toLex (HahnSeries.truncLTLinearMap K c (ofLex (seed.baseE
mbedding x))) in LinearMap.range seed.baseEmbedding.toFun
参数：x : seed.baseEmbedding.domain；c : FiniteArchimedeanClass M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_iSup_iff_exists_dfinsupp'`：mem_iSup_iff_exists_dfinsupp' (
p : ι -> Submodule R N) [forall (i) (x : p i), Decidable (x != 0)] (x : N) : x i
n iSup p ↔ exists f : Π₀ i, p…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnEmbedding.Seed.domain_baseEmbedding`：domain_baseEmbedding : seed.bas
eEmbedding.domain = seed.baseDomain
· 使用定理 `HahnEmbedding.ArchimedeanStrata.baseDomain.eq_1`：∀ {K : Type u_1} [inst 
: DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : 
Archimedean K]   {M : Type u_2} [inst…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `ofLex_toLex`：ofLex_toLex (a : α) : ofLex (toLex a) = a
· 使用定理 `LinearPMap.toFun_eq_coe`：toFun_eq_coe (f : E ->ₛₗ.[σ] F) (x : f.domain) 
: f.toFun x = f x
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HahnEmbedding.Seed.coeff_baseEmbedding`：coeff_baseEmbedding {x : seed.ba
seEmbedding.domain} {f : Π₀ c, seed.stratum c} (h : x.val = f.sum fun c => (seed
.stratum c).subtype) (c : Fi…
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `HahnSeries.coe_truncLTLinearMap`：coe_truncLTLinearMap [DecidableLT Γ] (c
 : Γ) : (truncLTLinearMap R c : V⟦Γ⟧ -> V⟦Γ⟧) = truncLT c
· 使用定理 `HahnSeries.coeff_truncLT_of_lt`：coeff_truncLT_of_lt [PartialOrder Γ] [De
cidableLT Γ] {c i : Γ} (h : i < c) (x : R⟦Γ⟧) : (truncLT c x).coeff i = x.coeff 
i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `HahnSeries.coeff_truncLT_of_le`：coeff_truncLT_of_le [LinearOrder Γ] {c i
 : Γ} (h : c <= i) (x : R⟦Γ⟧) : (truncLT c x).coeff i = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
（共 36 条，此处仅展示前 30 条）
-/
theorem truncLT_mem_range_baseEmbedding (x : seed.baseEmbedding.domain)
    (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (seed.baseEmbedding x))) ∈
    LinearMap.range seed.baseEmbedding.toFun := by
  -- decompose `x` to `stratum`
  have hmem : x.val ∈ seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  -- Truncating in the codomain is the same as truncating away some submodule
  let f' : Π₀ (i : FiniteArchimedeanClass M), seed.stratum i :=
    DFinsupp.mk f.support fun d ↦ if c.val ≤ d.val then 0 else f d.val
  refine ⟨⟨f'.sum fun d x ↦ x.val, ?_⟩, ?_⟩
  · rw [seed.domain_baseEmbedding, ArchimedeanStrata.baseDomain,
      Submodule.mem_iSup_iff_exists_dfinsupp']
    use f'
  apply_fun ofLex
  rw [ofLex_toLex, LinearPMap.toFun_eq_coe]
  ext d
  rw [seed.coeff_baseEmbedding rfl]
  unfold f'
  obtain hdc | hdc := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc,
      seed.coeff_baseEmbedding hf.symm]
    apply congrArg
    have hcd : ¬ c.val ≤ d.val := not_le_of_gt hdc
    simp only [DFinsupp.mk_apply, hcd, ↓reduceIte]
    aesop
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hdc]
    have hcd : c.val ≤ d.val := hdc
    simp only [DFinsupp.mk_apply, hcd, ↓reduceIte]
    convert! LinearMap.map_zero _
    simp

/-- `HahnEmbedding.Seed.baseEmbedding` is a partial Hahn embedding. -/
/-
**HahnEmbedding.Seed.isPartial_baseEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbe
dding.Seed`。
形式化陈述：isPartial_baseEmbedding [IsOrderedAddMonoid R] : IsPartial seed seed.baseE
mbedding where strictMono
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Seed.baseEmbedding_strictMono`：baseEmbedding_strictMono [I
sOrderedAddMonoid R] : StrictMono seed.baseEmbedding
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `HahnEmbedding.Seed.truncLT_mem_range_baseEmbedding`：truncLT_mem_range_ba
seEmbedding (x : seed.baseEmbedding.domain) (c : FiniteArchimedeanClass M) : toL
ex (HahnSeries.truncLTLinearMap K c (ofL…

--- 原说明 ---
`HahnEmbedding.Seed.baseEmbedding` is a partial Hahn embedding.
-/
theorem isPartial_baseEmbedding [IsOrderedAddMonoid R] : IsPartial seed seed.baseEmbedding where
  strictMono := seed.baseEmbedding_strictMono
  baseEmbedding_le := le_refl _
  truncLT_mem_range := seed.truncLT_mem_range_baseEmbedding

end Seed

/-- The type of all partial Hahn embeddings. -/
/-
**HahnEmbedding.Partial** 是 Mathlib 中的一个缩写定义，位于命名空间 `HahnEmbedding`。
形式化陈述：Partial
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of all partial Hahn embeddings.
-/
abbrev Partial := {f : M →ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ // IsPartial seed f}

namespace Partial
variable {seed} (f : Partial seed)

noncomputable
/-
**HahnEmbedding.Partial.** 是 Mathlib 中的一个实例，位于命名空间 `HahnEmbedding.Partial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsOrderedAddMonoid R] : Inhabited (Partial seed) where
  default := ⟨seed.baseEmbedding, seed.isPartial_baseEmbedding⟩

/-- `HahnEmbedding.Partial` as an `OrderedAddMonoidHom`. -/
/-
**HahnEmbedding.Partial.toOrderAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbed
ding.Partial`。
形式化陈述：toOrderAddMonoidHom : f.val.domain ->+o Lex R⟦FiniteArchimedeanClass M⟧ wh
ere __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HahnEmbedding.Partial` as an `OrderedAddMonoidHom`.
-/
noncomputable def toOrderAddMonoidHom : f.val.domain →+o Lex R⟦FiniteArchimedeanClass M⟧ where
  __ := f.val.toFun
  map_zero' := by simp
  monotone' := f.prop.strictMono.monotone
/-
**HahnEmbedding.Partial.toOrderAddMonoidHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Hah
nEmbedding.Partial`。
形式化陈述：toOrderAddMonoidHom_apply (x : f.val.domain) : f.toOrderAddMonoidHom x = f
.val x
参数：x : f.val.domain。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOrderAddMonoidHom_apply (x : f.val.domain) : f.toOrderAddMonoidHom x = f.val x := rfl
/-
**HahnEmbedding.Partial.toOrderAddMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 
`HahnEmbedding.Partial`。
形式化陈述：toOrderAddMonoidHom_injective : Function.Injective f.toOrderAddMonoidHom
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `HahnEmbedding.IsPartial.strictMono`：∀ {K : Type u_1} [inst : DivisionRin
g K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean K
]   {M : Type u_2} [inst…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem toOrderAddMonoidHom_injective : Function.Injective f.toOrderAddMonoidHom :=
  f.prop.strictMono.injective
/-
**HahnEmbedding.Partial.mem_domain** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.Part
ial`。
形式化陈述：mem_domain {x : M} {c : FiniteArchimedeanClass M} (hx : x in seed.stratum 
c) : x in f.val.domain
参数：hx : x in seed.stratum c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HahnEmbedding.IsPartial.baseEmbedding_le`：∀ {K : Type u_1} [inst : Divis
ionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archime
dean K]   {M : Type u_2} [inst…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `HahnEmbedding.Seed.mem_domain_baseEmbedding`：mem_domain_baseEmbedding {x
 : M} {c : FiniteArchimedeanClass M} (h : x in seed.stratum c) : x in seed.baseE
mbedding.domain
-/
theorem mem_domain {x : M} {c : FiniteArchimedeanClass M} (hx : x ∈ seed.stratum c) :
    x ∈ f.val.domain := by
  apply Set.mem_of_subset_of_mem f.prop.baseEmbedding_le.1
  apply seed.mem_domain_baseEmbedding hx
/-
**HahnEmbedding.Partial.apply_of_mem_stratum** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbe
dding.Partial`。
形式化陈述：apply_of_mem_stratum {x : f.val.domain} {c : FiniteArchimedeanClass M} (hx
 : x.val in seed.stratum c) : f.val x = toLex (HahnSeries.single c (seed.coeff c
 ⟨x.val, hx⟩))
参数：hx : x.val in seed.stratum c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Seed.mem_domain_baseEmbedding`：mem_domain_baseEmbedding {x
 : M} {c : FiniteArchimedeanClass M} (h : x in seed.stratum c) : x in seed.baseE
mbedding.domain
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `HahnEmbedding.IsPartial.baseEmbedding_le`：∀ {K : Type u_1} [inst : Divis
ionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archime
dean K]   {M : Type u_2} [inst…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.sum_single_index`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x 
: β i) → Decida…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `ofLex_toLex`：ofLex_toLex (a : α) : ofLex (toLex a) = a
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HahnEmbedding.Seed.coeff_baseEmbedding`：coeff_baseEmbedding {x : seed.ba
seEmbedding.domain} {f : Π₀ c, seed.stratum c} (h : x.val = f.sum fun c => (seed
.stratum c).subtype) (c : Fi…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `HahnSeries.coeff_single_same`：coeff_single_same (a : Γ) (r : R) : (singl
e a r).coeff a = r
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `HahnSeries.coeff_single_of_ne`：coeff_single_of_ne (h : b != a) : (single
 a r).coeff b = 0
-/
theorem apply_of_mem_stratum {x : f.val.domain} {c : FiniteArchimedeanClass M}
    (hx : x.val ∈ seed.stratum c) :
    f.val x = toLex (HahnSeries.single c (seed.coeff c ⟨x.val, hx⟩)) := by
  have hx' : x.val ∈ seed.baseEmbedding.domain := seed.mem_domain_baseEmbedding hx
  have heq : (⟨x.val, hx'⟩ : seed.baseEmbedding.domain).val = x.val := rfl
  rw [← f.prop.baseEmbedding_le.2 heq]
  let fx : Π₀ c, seed.stratum c := DFinsupp.single c ⟨x.val, hx⟩
  have hfx : x.val = fx.sum fun c ↦ (seed.stratum c).subtype := by
    simp [fx, DFinsupp.sum_single_index]
  apply_fun ofLex
  rw [ofLex_toLex]
  ext d
  rw [seed.coeff_baseEmbedding hfx]
  unfold fx
  obtain rfl | hdc := eq_or_ne d c
  · simp
  simp [HahnSeries.coeff_single_of_ne hdc, hdc.symm]

open ArchimedeanClass in
/-- Archimedean equivalence is preserved by `f`. -/
/-
**HahnEmbedding.Partial.archimedeanClassMk_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Hah
nEmbedding.Partial`。
形式化陈述：archimedeanClassMk_eq_iff [IsOrderedAddMonoid R] (x y : f.val.domain) : Ar
chimedeanClass.mk (f.val x) = .mk (f.val y) ↔ ArchimedeanClass.mk x.val = .mk y.
val
参数：x y : f.val.domain。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `ArchimedeanClass.orderHom_injective`：∀ {M : Type u_1} [inst : AddCommGro
up M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {N : Type u_2}   
[inst_3 : AddCommGroup N]…
· 使用定理 `HahnEmbedding.Partial.toOrderAddMonoidHom_injective`：toOrderAddMonoidHom
_injective : Function.Injective f.toOrderAddMonoidHom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Archimedean equivalence is preserved by `f`.
-/
theorem archimedeanClassMk_eq_iff [IsOrderedAddMonoid R] (x y : f.val.domain) :
    ArchimedeanClass.mk (f.val x) = .mk (f.val y) ↔ ArchimedeanClass.mk x.val = .mk y.val := by
  simp_rw [← toOrderAddMonoidHom_apply, ← orderHom_mk]
  trans ArchimedeanClass.mk x = .mk y
  · exact Function.Injective.eq_iff <| orderHom_injective <| toOrderAddMonoidHom_injective _
  · simp_rw [mk_eq_mk]
    aesop

/-- Archimedean equivalence of input is transferred to `HahnSeries.orderTop` equality. -/
/-
**HahnEmbedding.Partial.orderTop_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding
.Partial`。
形式化陈述：orderTop_eq_iff [IsOrderedAddMonoid R] [Archimedean R] (x y : f.val.domain
) : (ofLex (f.val x)).orderTop = (ofLex (f.val y)).orderTop ↔ ArchimedeanClass.m
k x.val = .mk y.val
参数：x y : f.val.domain。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Subsingleton.allEq`：∀ {α : Sort u} [self : Subsingleton α] (a b : α), a 
= b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `FiniteArchimedeanClass.instNonemptyOfNontrivial`：∀ {M : Type u_1} [inst 
: AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] [Nont
rivial M],   Nonempty (FiniteArchimed…
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `HahnEmbedding.Seed.strictMono_coeff`：∀ {K : Type u_1} [inst : DivisionRi
ng K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean 
K]   {M : Type u_2} [inst…
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnEmbedding.Partial.archimedeanClassMk_eq_iff`：archimedeanClassMk_eq_i
ff [IsOrderedAddMonoid R] (x y : f.val.domain) : ArchimedeanClass.mk (f.val x) =
 .mk (f.val y) ↔ ArchimedeanClass.mk …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Archimedean equivalence of input is transferred to `HahnSeries.orderTop` equalit
y.
-/
theorem orderTop_eq_iff [IsOrderedAddMonoid R] [Archimedean R] (x y : f.val.domain) :
    (ofLex (f.val x)).orderTop = (ofLex (f.val y)).orderTop ↔
    ArchimedeanClass.mk x.val = .mk y.val := by
  obtain hsubsingleton | hnontrivial := subsingleton_or_nontrivial M
  · have : y = x := Subtype.ext <| hsubsingleton.allEq _ _
    simp [this]
  have hnonempty : Nonempty (FiniteArchimedeanClass M) := inferInstance
  obtain c := hnonempty.some
  have : Nontrivial R := (seed.strictMono_coeff c).injective.nontrivial
  rw [← archimedeanClassMk_eq_iff]
  simp_rw [← HahnSeries.archimedeanClassOrderIsoWithTop_apply]
  rw [(HahnSeries.archimedeanClassOrderIsoWithTop (FiniteArchimedeanClass M) R).injective.eq_iff]

/-- Archimedean class of the input is transferred to `HahnSeries.orderTop`. -/
/-
**HahnEmbedding.Partial.orderTop_eq_archimedeanClassMk** 是 Mathlib 中的一个定理，位于命名空间
 `HahnEmbedding.Partial`。
形式化陈述：orderTop_eq_archimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R] (x :
 f.val.domain) : FiniteArchimedeanClass.withTopOrderIso M (ofLex (f.val x)).orde
rTop = .mk x.val
参数：x : f.val.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.map_zero`：map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0
· 使用定理 `HahnSeries.orderTop_zero`：orderTop_zero : orderTop (0 : R⟦Γ⟧) = ⊤
· 使用定理 `TopHomClass.map_top`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Top α} {inst_1 : Top β}   {inst_2 : FunLike F α β} [se
lf : TopH…
· 使用定理 `InfTopHomClass.toTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Min α] [inst_2 : Min β] [inst_3 : Top α]  
 [inst_4 : Top β] …
· 使用定理 `OrderIsoClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : OrderTop
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `HahnEmbedding.ArchimedeanStrata.archimedeanClassMk_of_mem_stratum`：archi
medeanClassMk_of_mem_stratum {a : M} (ha : a in u.stratum c) (h0 : a != 0) : Arc
himedeanClass.mk a = c
· 使用定理 `HahnEmbedding.Partial.mem_domain`：mem_domain {x : M} {c : FiniteArchimed
eanClass M} (hx : x in seed.stratum c) : x in f.val.domain
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `LinearMap.map_eq_zero_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8
} {M₃ : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddComm
Monoid M] [inst…
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `HahnEmbedding.Seed.strictMono_coeff`：∀ {K : Type u_1} [inst : DivisionRi
ng K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean 
K]   {M : Type u_2} [inst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.orderTop_single`：orderTop_single (h : r != 0) : (single a r).
orderTop = a
· 使用定理 `ofLex_toLex`：ofLex_toLex (a : α) : ofLex (toLex a) = a
· 使用定理 `HahnEmbedding.Partial.apply_of_mem_stratum`：apply_of_mem_stratum {x : f.
val.domain} {c : FiniteArchimedeanClass M} (hx : x.val in seed.stratum c) : f.va
l x = toLex (HahnSeries.single c…
· 使用定理 `HahnEmbedding.Partial.orderTop_eq_iff`：orderTop_eq_iff [IsOrderedAddMono
id R] [Archimedean R] (x y : f.val.domain) : (ofLex (f.val x)).orderTop = (ofLex
 (f.val y)).orderTop ↔ Arch…
· 使用定理 `FiniteArchimedeanClass.withTopOrderIso_apply_coe`：∀ {M : Type u_1} [inst
 : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M]   (A
 : FiniteArchimedeanClass M), (FiniteA…

--- 原说明 ---
Archimedean class of the input is transferred to `HahnSeries.orderTop`.
-/
theorem orderTop_eq_archimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R] (x : f.val.domain) :
    FiniteArchimedeanClass.withTopOrderIso M (ofLex (f.val x)).orderTop = .mk x.val := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : x.val ≠ 0 := by simpa using hx0
  -- Pick a representative `x'` from `stratum` with the same class as `x`.
  -- `f.val x'` is a `HahnSeries.single` whose `orderTop` is known
  obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : seed.stratum (.mk x hx0'))
  have heq : ArchimedeanClass.mk x' = .mk x.val := by
    apply seed.archimedeanClassMk_of_mem_stratum hx'mem
    simpa using hx'0
  let x'' : f.val.domain := ⟨x', mem_domain f hx'mem⟩
  have hx''mem : x''.val ∈ seed.stratum (mk x.val hx0') := hx'mem
  have h0 : (seed.coeff (mk x.val hx0')) ⟨x''.val, hx''mem⟩ ≠ 0 := by
    rw [(LinearMap.map_eq_zero_iff _ (seed.strictMono_coeff _).injective).ne]
    unfold x''
    simpa using hx'0
  have heq' : ArchimedeanClass.mk x''.val = .mk x.val := heq
  rw [← orderTop_eq_iff, apply_of_mem_stratum f hx''mem, ofLex_toLex,
    HahnSeries.orderTop_single h0] at heq'
  simp [← heq']
/-
**HahnEmbedding.Partial.orderTop_eq_finiteArchimedeanClassMk** 是 Mathlib 中的一个定理，
位于命名空间 `HahnEmbedding.Partial`。
形式化陈述：orderTop_eq_finiteArchimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R
] {x : f.val.domain} (hx0 : x.val != 0) : (ofLex (f.val x)).orderTop = FiniteArc
himedeanClass.mk x.val hx0
参数：hx0 : x.val != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnEmbedding.Partial.orderTop_eq_archimedeanClassMk`：orderTop_eq_archim
edeanClassMk [IsOrderedAddMonoid R] [Archimedean R] (x : f.val.domain) : FiniteA
rchimedeanClass.withTopOrderIso M (ofLex (…
· 使用定理 `FiniteArchimedeanClass.withTopOrderIso_apply_coe`：∀ {M : Type u_1} [inst
 : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M]   (A
 : FiniteArchimedeanClass M), (FiniteA…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orderTop_eq_finiteArchimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R]
    {x : f.val.domain} (hx0 : x.val ≠ 0) :
    (ofLex (f.val x)).orderTop = FiniteArchimedeanClass.mk x.val hx0 := by
  apply_fun FiniteArchimedeanClass.withTopOrderIso M
  simp [orderTop_eq_archimedeanClassMk]

/-- For `x` within a ball of Archimedean class `c`, `f.val x`'coefficient at `d` vanishes
for `d ≤ c`. -/
/-
**HahnEmbedding.Partial.coeff_eq_zero_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbe
dding.Partial`。
形式化陈述：coeff_eq_zero_of_mem [IsOrderedAddMonoid R] [Archimedean R] {c : FiniteArc
himedeanClass M} {x : f.val.domain} (hx : x.val in ball K c) {d : FiniteArchimed
eanClass M} (hd : d.val <= c) : (ofLex (f.val x)).coeff d = 0
参数：hx : x.val in ball K c；hd : d.val <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.map_zero`：map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.coeff_eq_zero_of_lt_orderTop`：coeff_eq_zero_of_lt_orderTop {x
 : R⟦Γ⟧} {i : Γ} (hi : i < x.orderTop) : x.coeff i = 0
· 使用定理 `Mathlib.Tactic.ApplyFun.lt_of_lt`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] (e : α ≃o β) {x y : α}, e x < e y → x < y
· 使用定理 `HahnEmbedding.Partial.orderTop_eq_archimedeanClassMk`：orderTop_eq_archim
edeanClassMk [IsOrderedAddMonoid R] [Archimedean R] (x : f.val.domain) : FiniteA
rchimedeanClass.withTopOrderIso M (ofLex (…
· 使用定理 `FiniteArchimedeanClass.withTopOrderIso_apply_coe`：∀ {M : Type u_1} [inst
 : AddCommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M]   (A
 : FiniteArchimedeanClass M), (FiniteA…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M

--- 原说明 ---
For `x` within a ball of Archimedean class `c`, `f.val x`'coefficient at `d` van
ishes
for `d ≤ c`.
-/
theorem coeff_eq_zero_of_mem [IsOrderedAddMonoid R] [Archimedean R]
    {c : FiniteArchimedeanClass M} {x : f.val.domain} (hx : x.val ∈ ball K c)
    {d : FiniteArchimedeanClass M} (hd : d.val ≤ c) : (ofLex (f.val x)).coeff d = 0 := by
  obtain rfl | ne := eq_or_ne x 0
  · simp
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  apply_fun FiniteArchimedeanClass.withTopOrderIso _
  rw [orderTop_eq_archimedeanClassMk, FiniteArchimedeanClass.withTopOrderIso_apply_coe]
  apply lt_of_le_of_lt hd
  simpa using! hx (by simpa using! ne)

/-- `f.val x` has a non-zero coefficient at the position of the Archimedean class of `x`. -/
/-
**HahnEmbedding.Partial.coeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.P
artial`。
形式化陈述：coeff_ne_zero [IsOrderedAddMonoid R] [Archimedean R] {x : f.val.domain} (h
x0 : x.val != 0) : (ofLex (f.val x)).coeff (FiniteArchimedeanClass.mk x.val hx0)
 != 0
参数：hx0 : x.val != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnSeries.coeff_orderTop_ne`：coeff_orderTop_ne {x : R⟦Γ⟧} {g : Γ} (hg :
 x.orderTop = g) : x.coeff g != 0
· 使用定理 `HahnEmbedding.Partial.orderTop_eq_finiteArchimedeanClassMk`：orderTop_eq_
finiteArchimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R] {x : f.val.domai
n} (hx0 : x.val != 0) : (ofLex (f.val x)).orderT…

--- 原说明 ---
`f.val x` has a non-zero coefficient at the position of the Archimedean class of
 `x`.
-/
theorem coeff_ne_zero [IsOrderedAddMonoid R] [Archimedean R] {x : f.val.domain} (hx0 : x.val ≠ 0) :
    (ofLex (f.val x)).coeff (FiniteArchimedeanClass.mk x.val hx0) ≠ 0 :=
  HahnSeries.coeff_orderTop_ne <| f.orderTop_eq_finiteArchimedeanClassMk hx0

/-- When `y` and `z` are both near `x` (the difference is in a ball),
initial coefficients of `f.val y` and `f.val z` agree. -/
/-
**HahnEmbedding.Partial.coeff_eq_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding
.Partial`。
形式化陈述：coeff_eq_of_mem [IsOrderedAddMonoid R] [Archimedean R] (x : M) {y z : f.va
l.domain} {c : FiniteArchimedeanClass M} (hy : y.val - x in ball K c) (hz : z.va
l - x in ball K c) {d : FiniteArchimedeanClass M} (hd : d <= c) : (ofLex (f.val 
y)).coeff d = (ofLex (f.val z)).coeff d
参数：x : M；hy : y.val - x in ball K c；hz : z.val - x in ball K c；hd : d <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnSeries.coeff_sub`：coeff_sub {x y : R⟦Γ⟧} {a : Γ} : (x - y).coeff a =
 x.coeff a - y.coeff a
· 使用定理 `ofLex_sub`：∀ {α : Type u_1} [inst : Sub α] (a b : Lex α), ofLex (a - b) 
= ofLex a - ofLex b
· 使用定理 `LinearPMap.map_sub`：map_sub (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x -
 y) = f x - f y
· 使用定理 `HahnEmbedding.Partial.coeff_eq_zero_of_mem`：coeff_eq_zero_of_mem [IsOrde
redAddMonoid R] [Archimedean R] {c : FiniteArchimedeanClass M} {x : f.val.domain
} (hx : x.val in ball K c) {d : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …

--- 原说明 ---
When `y` and `z` are both near `x` (the difference is in a ball),
initial coefficients of `f.val y` and `f.val z` agree.
-/
theorem coeff_eq_of_mem [IsOrderedAddMonoid R] [Archimedean R] (x : M) {y z : f.val.domain}
    {c : FiniteArchimedeanClass M} (hy : y.val - x ∈ ball K c) (hz : z.val - x ∈ ball K c)
    {d : FiniteArchimedeanClass M} (hd : d ≤ c) :
    (ofLex (f.val y)).coeff d = (ofLex (f.val z)).coeff d := by
  apply eq_of_sub_eq_zero
  rw [← HahnSeries.coeff_sub, ← ofLex_sub, ← LinearPMap.map_sub]
  refine coeff_eq_zero_of_mem f ?_ hd
  have : (y - z).val = (y.val - x) - (z.val - x) := by
    push_cast
    simp
  rw [this]
  exact Submodule.sub_mem _ hy hz

/-! ### Step 3: extend the embedding

We create a larger `HahnEmbedding.Partial` from an existing one by adding a new element to the
domain and assigning an appropriate output that preserves all `HahnEmbedding.Partial`'s properties.
-/

/-- Evaluate coefficients of the `HahnSeries` given an arbitrary input that's not necessarily in
`f`'s domain. The coefficient is picked from `y` that is "close enough" to `x` (their difference
is in a higher `ArchimedeanClass`). If no such `y` exists (in other words, x is "isolated"), set the
coefficient to 0.

This doesn't immediately extend `f`'s domain to the entire module in a consistent way. Such
extension isn't necessarily linear.
-/
noncomputable
/-
**HahnEmbedding.Partial.evalCoeff** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbedding.Parti
al`。
形式化陈述：evalCoeff (x : M) (c : FiniteArchimedeanClass M) : R
参数：x : M；c : FiniteArchimedeanClass M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def evalCoeff (x : M) (c : FiniteArchimedeanClass M) : R :=
  open scoped Classical in
  if h : ∃ y : f.val.domain, y.val - x ∈ ball K c then
    (ofLex (f.val h.choose)).coeff c
  else
    0

/-- The coefficient is well-defined regardless of which `y` we pick in `evalCoeff`. -/
/-
**HahnEmbedding.Partial.evalCoeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.Pa
rtial`。
形式化陈述：evalCoeff_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M} {c : FiniteArc
himedeanClass M} {y : f.val.domain} (hy : y.val - x in ball K c) : evalCoeff f x
 c = (ofLex (f.val y)).coeff c
参数：hy : y.val - x in ball K c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `HahnEmbedding.Partial.coeff_eq_of_mem`：coeff_eq_of_mem [IsOrderedAddMono
id R] [Archimedean R] (x : M) {y z : f.val.domain} {c : FiniteArchimedeanClass M
} (hy : y.val - x in ball K…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The coefficient is well-defined regardless of which `y` we pick in `evalCoeff`.
-/
theorem evalCoeff_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M} {c : FiniteArchimedeanClass M}
    {y : f.val.domain} (hy : y.val - x ∈ ball K c) :
    evalCoeff f x c = (ofLex (f.val y)).coeff c := by
  have hnonempty : ∃ y : f.val.domain, y.val - x ∈ ball K c := ⟨y, hy⟩
  simpa [evalCoeff, dif_pos hnonempty] using coeff_eq_of_mem f x hnonempty.choose_spec hy le_rfl
/-
**HahnEmbedding.Partial.evalCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbeddi
ng.Partial`。
形式化陈述：evalCoeff_eq_zero {x : M} {c : FiniteArchimedeanClass M} (h : ¬exists y : 
f.val.domain, y.val - x in ball K c) : f.evalCoeff x c = 0
参数：h : ¬exists y : f.val.domain, y.val - x in ball K c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnEmbedding.Partial.evalCoeff.eq_1`：∀ {K : Type u_1} [inst : DivisionR
ing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean
 K]   {M : Type u_2} [inst…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem evalCoeff_eq_zero {x : M} {c : FiniteArchimedeanClass M}
    (h : ¬∃ y : f.val.domain, y.val - x ∈ ball K c) :
    f.evalCoeff x c = 0 := by
  rw [evalCoeff, dif_neg h]
/-
**HahnEmbedding.Partial.isWF_support_evalCoeff** 是 Mathlib 中的一个定理，位于命名空间 `HahnEm
bedding.Partial`。
形式化陈述：isWF_support_evalCoeff [IsOrderedAddMonoid R] [Archimedean R] (x : M) : (e
valCoeff f x).support.IsWF
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.isWF_iff_no_descending_seq`：isWF_iff_no_descending_seq : IsWF s ↔ fo
rall f : Nat -> α, StrictAnti f -> ¬forall n, f n in s
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnEmbedding.Partial.evalCoeff_eq`：evalCoeff_eq [IsOrderedAddMonoid R] 
[Archimedean R] {x : M} {c : FiniteArchimedeanClass M} {y : f.val.domain} (hy : 
y.val - x in ball K c) :…
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
· 使用定理 `FiniteArchimedeanClass.ball_strictAnti`：ball_strictAnti : StrictAnti (ba
ll (M
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `HahnSeries.isWF_support`：isWF_support (x : R⟦Γ⟧) : x.support.IsWF
-/
theorem isWF_support_evalCoeff [IsOrderedAddMonoid R] [Archimedean R] (x : M) :
    (evalCoeff f x).support.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  by_contra! ⟨seq, ⟨hanti, hmem⟩⟩
  have hnonempty : ∃ y : f.val.domain, y.val - x ∈ ball K (seq 0) := by
    specialize hmem 0
    contrapose hmem with hempty
    simp [evalCoeff, dif_neg hempty]
  obtain ⟨y, hy⟩ := hnonempty
  have hmem' (n : ℕ) : seq n ∈ (ofLex (f.val y)).coeff.support := by
    specialize hmem n
    rw [Function.mem_support] at ⊢ hmem
    convert hmem
    refine (f.evalCoeff_eq ((ball_strictAnti K).antitone ?_ hy)).symm
    simpa using hanti.antitone (show 0 ≤ n by simp)
  obtain hwf := (ofLex (f.val y)).isWF_support
  contrapose! hwf
  rw [Set.isWF_iff_no_descending_seq]
  simpa using ⟨seq, hanti, hmem'⟩

/-- Promote `HahnEmbedding.Partial.evalCoeff`'s output to a new `HahnSeries`. -/
noncomputable
/-
**HahnEmbedding.Partial.eval** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbedding.Partial`。
形式化陈述：eval [IsOrderedAddMonoid R] [Archimedean R] (x : M) : Lex R⟦FiniteArchimed
eanClass M⟧
参数：x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def eval [IsOrderedAddMonoid R] [Archimedean R] (x : M) :
    Lex R⟦FiniteArchimedeanClass M⟧ :=
  toLex { coeff := f.evalCoeff x
          isPWO_support' := (f.isWF_support_evalCoeff x).isPWO }

@[simp]
/-
**HahnEmbedding.Partial.eval_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.Parti
al`。
形式化陈述：eval_zero [IsOrderedAddMonoid R] [Archimedean R] : f.eval 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnEmbedding.Partial.evalCoeff_eq`：evalCoeff_eq [IsOrderedAddMonoid R] 
[Archimedean R] {x : M} {c : FiniteArchimedeanClass M} {y : f.val.domain} (hy : 
y.val - x in ball K c) :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearPMap.map_zero`：map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HahnSeries.isPWO_support'`：∀ {Γ : Type u_1} {R : Type u_2} [inst : Parti
alOrder Γ] [inst_1 : Zero R] (self : HahnSeries Γ R),   (Function.support self.c
oeff).IsPWO
· 使用定理 `toLex_zero`：∀ {α : Type u_1} [inst : Zero α], toLex 0 = 0
-/
theorem eval_zero [IsOrderedAddMonoid R] [Archimedean R] : f.eval 0 = 0 := by
  unfold eval
  convert! toLex_zero
  ext c
  rw [f.evalCoeff_eq (y := 0) (by simp)]
  simp
/-
**HahnEmbedding.Partial.eval_smul** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.Parti
al`。
形式化陈述：eval_smul [IsOrderedAddMonoid R] [Archimedean R] (k : K) (x : M) : f.eval 
(k • x) = k • f.eval x
参数：k : K；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnEmbedding.Partial.eval.congr_simp`：∀ {K : Type u_1} [inst : Division
Ring K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedea
n K]   {M : Type u_2} [inst…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `HahnEmbedding.Partial.eval_zero`：eval_zero [IsOrderedAddMonoid R] [Archi
medean R] : f.eval 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `toLex_smul`：∀ {β : Type u_2} {α : Type u_1} [inst : SMul β α] (b : β) (a
 : α), toLex (b • a) = b • toLex a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `HahnEmbedding.Partial.evalCoeff_eq`：evalCoeff_eq [IsOrderedAddMonoid R] 
[Archimedean R] {x : M} {c : FiniteArchimedeanClass M} {y : f.val.domain} (hy : 
y.val - x in ball K c) :…
· 使用定理 `LinearPMap.map_smul`：map_smul [Module R F] (f : E ->ₗ.[R] F) (c : R) (x 
: f.domain) : f (c • x) = c • f x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `HahnEmbedding.Partial.evalCoeff_eq_zero`：evalCoeff_eq_zero {x : M} {c : 
FiniteArchimedeanClass M} (h : ¬exists y : f.val.domain, y.val - x in ball K c) 
: f.evalCoeff x c = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem eval_smul [IsOrderedAddMonoid R] [Archimedean R] (k : K) (x : M) :
    f.eval (k • x) = k • f.eval x := by
  by_cases hk : k = 0
  · simp [hk]
  unfold eval
  rw [← toLex_smul, toLex.injective.eq_iff]
  ext c
  suffices f.evalCoeff (k • x) c = k • f.evalCoeff x c by simpa using this
  by_cases h : ∃ y : f.val.domain, y.val - x ∈ ball K c
  · obtain ⟨y, hy⟩ := h
    have heq : (k • y).val - k • x = k • (y.val - x) := by simp [smul_sub]
    have hy' : (k • y).val - k • x ∈ ball K c := by
      rw [heq]
      exact Submodule.smul_mem _ _ hy
    simp [f.evalCoeff_eq hy, f.evalCoeff_eq hy', LinearPMap.map_smul]
  have h' : ¬∃ y : f.val.domain, y.val - k • x ∈ ball K c := by
    contrapose h
    obtain ⟨y, hy⟩ := h
    use k⁻¹ • y
    have heq : (k⁻¹ • y).val - x = k⁻¹ • (y.val - k • x) := by
      simp [smul_sub, smul_smul, inv_mul_cancel₀ hk]
    exact heq ▸ Submodule.smul_mem _ _ hy
  simp [f.evalCoeff_eq_zero h, f.evalCoeff_eq_zero h']

/-- If `f.eval x = f.val y`, then for any `z` in the domain, `x - z` can't be closer than `x - y`
in terms of Archimedean classes. -/
/-
**HahnEmbedding.Partial.archimedeanClassMk_le_of_eval_eq** 是 Mathlib 中的一个定理，位于命名
空间 `HahnEmbedding.Partial`。
形式化陈述：archimedeanClassMk_le_of_eval_eq [IsOrderedAddMonoid R] [Archimedean R] {x
 : M} {y : f.val.domain} (h : f.eval x = f.val y) (z : f.val.domain) : Archimede
anClass.mk (x - z.val) <= .mk (x - y.val)
参数：h : f.eval x = f.val y；z : f.val.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Order.Module.HahnEmbedding.0.HahnEmbedding.Part
ial.archimedeanClassMk_le_of_eval_eq._abel_1_1`：∀ {K : Type u_2} [inst : Divisio
nRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimede
an K]   {M : Type u_1} [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ArchimedeanClass.mk_left_le_mk_add`：∀ {M : Type u_1} [inst : AddCommGrou
p M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M},   Archi
medeanClass.mk a ≤ Archi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnEmbedding.Partial.evalCoeff_eq`：evalCoeff_eq [IsOrderedAddMonoid R] 
[Archimedean R] {x : M} {c : FiniteArchimedeanClass M} {y : f.val.domain} (hy : 
y.val - x in ball K c) :…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `ArchimedeanClass.mk_sub_comm`：∀ {M : Type u_1} [inst : AddCommGroup M] [
inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] (a b : M),   Archimedean
Class.mk (a - b) =…
· 使用定理 `LinearPMap.map_sub`：map_sub (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x -
 y) = f x - f y
· 使用定理 `ofLex_sub`：∀ {α : Type u_1} [inst : Sub α] (a b : Lex α), ofLex (a - b) 
= ofLex a - ofLex b
· 使用定理 `HahnSeries.coeff_sub`：coeff_sub {x y : R⟦Γ⟧} {a : Γ} : (x - y).coeff a =
 x.coeff a - y.coeff a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HahnEmbedding.Partial.coeff_ne_zero`：coeff_ne_zero [IsOrderedAddMonoid R
] [Archimedean R] {x : f.val.domain} (hx0 : x.val != 0) : (ofLex (f.val x)).coef
f (FiniteArchimedeanClass…

--- 原说明 ---
If `f.eval x = f.val y`, then for any `z` in the domain, `x - z` can't be closer
 than `x - y`
in terms of Archimedean classes.
-/
theorem archimedeanClassMk_le_of_eval_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    {y : f.val.domain} (h : f.eval x = f.val y) (z : f.val.domain) :
    ArchimedeanClass.mk (x - z.val) ≤ .mk (x - y.val) := by
  have : x - y.val = x - z.val + (z.val - y.val) := by abel
  rw [this]
  apply ArchimedeanClass.mk_left_le_mk_add
  by_cases hyz : z.val - y.val = 0
  · simp [hyz]
  have h1 (c : FiniteArchimedeanClass M) (hc : c.val < .mk (x - z.val)) :
      (ofLex (f.eval x)).coeff c = (ofLex (f.val z)).coeff c := by
    rw [ArchimedeanClass.mk_sub_comm] at hc
    simp_rw [eval, ofLex_toLex]
    apply evalCoeff_eq
    simpa [c.prop] using! fun _ ↦ hc
  have h2 : ∀ c : FiniteArchimedeanClass M, c.val < .mk (x - z.val) →
      (ofLex (f.val (z - y))).coeff c = 0 := by
    intro c hc
    rw [LinearPMap.map_sub, ofLex_sub, HahnSeries.coeff_sub, sub_eq_zero, ← h]
    exact (h1 c hc).symm
  contrapose! h2
  exact ⟨FiniteArchimedeanClass.mk (z.val - y.val) hyz, h2, coeff_ne_zero _ _⟩
/-
**HahnEmbedding.Partial.val_sub_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding
.Partial`。
形式化陈述：val_sub_ne_zero {x : M} (hx : x ∉ f.val.domain) (y : f.val.domain) : y.val
 - x != 0
参数：hx : x ∉ f.val.domain；y : f.val.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
-/
theorem val_sub_ne_zero {x : M} (hx : x ∉ f.val.domain) (y : f.val.domain) : y.val - x ≠ 0 := by
  contrapose hx
  obtain rfl : x = y.val := (sub_eq_zero.mp hx).symm
  simp

/-- If `x` isn't in `f`'s domain, `f.eval x` produces a brand new value not in `f`'s range. -/
/-
**HahnEmbedding.Partial.eval_ne** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.Partial
`。
形式化陈述：eval_ne [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.dom
ain) (y : f.val.domain) : f.eval x != f.val y
参数：hx : x ∉ f.val.domain；y : f.val.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Partial.val_sub_ne_zero`：val_sub_ne_zero {x : M} (hx : x ∉
 f.val.domain) (y : f.val.domain) : y.val - x != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `HahnEmbedding.ArchimedeanStrata.ball_sup_stratum_eq`：∀ {K : Type u_1} [i
nst : DivisionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_
3 : Archimedean K]   {M : Type u_2} [inst…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `HahnEmbedding.Partial.mem_domain`：mem_domain {x : M} {c : FiniteArchimed
eanClass M} (hx : x in seed.stratum c) : x in f.val.domain
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `FiniteArchimedeanClass.mem_ball_iff`：mem_ball_iff {a : M} {c : FiniteArc
himedeanClass M} : a in ball K c ↔ forall h : a != 0, c < mk a h
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `FiniteArchimedeanClass.mk_lt_mk`：∀ {M : Type u_1} [inst : AddCommGroup M
] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a : M} (ha : a ≠ 0) 
  {b : M} (hb : b ≠ 0…
· 使用定理 `HahnEmbedding.Partial.archimedeanClassMk_le_of_eval_eq`：archimedeanClass
Mk_le_of_eval_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M} {y : f.val.domai
n} (h : f.eval x = f.val y) (z : f.val.domai…

--- 原说明 ---
If `x` isn't in `f`'s domain, `f.eval x` produces a brand new value not in `f`'s
 range.
-/
theorem eval_ne [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) : f.eval x ≠ f.val y := by
  -- decompose `x - y = u + v`, where `v ∈ submodule (x - y)` and
  -- `u` is at higher class than `x - y`
  have := val_sub_ne_zero f hx y
  rw [sub_ne_zero, ne_comm, ← sub_ne_zero] at this
  let xy := mk _ this
  have hxy : x - y.val ∈ closedBall K xy := fun _ ↦ by simp; rfl
  rw [← seed.ball_sup_stratum_eq xy, Submodule.mem_sup] at hxy
  obtain ⟨u, hu, v, hv, huv⟩ := hxy
  have huv' : x - y.val - v = u := by simp [← huv]
  rw [mem_ball_iff K] at hu
  -- `z = x - u = y + v` is also in the domain.
  -- Assuming `f.eval x = f.val y` allows us to use `archimedeanClassMk_le_of_eval_eq` on `z`
  have hyv : y.val + v ∈ f.val.domain := Submodule.add_mem _ (by simp) (f.mem_domain hv)
  by_contra! h
  obtain h := f.archimedeanClassMk_le_of_eval_eq h ⟨y.val + v, hyv⟩
  contrapose! h
  simp_rw [← sub_sub, huv']
  obtain rfl | ne := eq_or_ne u 0
  exacts [Ne.lt_top (by simpa), (mk_lt_mk ..).mp (hu ne)]

/-- If there is a `y` in `f`'s domain with `c = ArchimedeanClass (y - x)`, but there
is no closer `z` to `x` where the difference is of a higher `ArchimedeanClass`, then
`f.eval x` is simply `f.val y` truncated at `c`.

This doesn't mean every `x` can be evaluated this way: it is possible that one can find
an infinite chain of `y` that keeps getting closer to `x` in terms of Archimedean classes,
yet `x` is still isolated within a very high Archimedean class. In fact, in the next theorem,
we will show that there is always such chain for `x` not in `f`'s domain. -/
/-
**HahnEmbedding.Partial.eval_eq_truncLT** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding
.Partial`。
形式化陈述：eval_eq_truncLT [IsOrderedAddMonoid R] [Archimedean R] {x : M} {c : Finite
ArchimedeanClass M} {y : f.val.domain} (hy : ArchimedeanClass.mk (y.val - x) = c
.val) (h : forall z : f.val.domain, z.val - x ∉ ball K c) : f.eval x = toLex (Ha
hnSeries.truncLTLinearMap K c (ofLex (f.val y)))
参数：hy : ArchimedeanClass.mk (y.val - x) = c.val；h : forall z : f.val.domain, z.v
al - x ∉ ball K c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `HahnSeries.coe_truncLTLinearMap`：coe_truncLTLinearMap [DecidableLT Γ] (c
 : Γ) : (truncLTLinearMap R c : V⟦Γ⟧ -> V⟦Γ⟧) = truncLT c
· 使用定理 `HahnSeries.coeff_truncLT_of_lt`：coeff_truncLT_of_lt [PartialOrder Γ] [De
cidableLT Γ] {c i : Γ} (h : i < c) (x : R⟦Γ⟧) : (truncLT c x).coeff i = x.coeff 
i
· 使用定理 `HahnEmbedding.Partial.evalCoeff_eq`：evalCoeff_eq [IsOrderedAddMonoid R] 
[Archimedean R] {x : M} {c : FiniteArchimedeanClass M} {y : f.val.domain} (hy : 
y.val - x in ball K c) :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `HahnSeries.coeff_truncLT_of_le`：coeff_truncLT_of_le [LinearOrder Γ] {c i
 : Γ} (h : c <= i) (x : R⟦Γ⟧) : (truncLT c x).coeff i = 0
· 使用定理 `HahnEmbedding.Partial.evalCoeff_eq_zero`：evalCoeff_eq_zero {x : M} {c : 
FiniteArchimedeanClass M} (h : ¬exists y : f.val.domain, y.val - x in ball K c) 
: f.evalCoeff x c = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
· 使用定理 `FiniteArchimedeanClass.ball_strictAnti`：ball_strictAnti : StrictAnti (ba
ll (M

--- 原说明 ---
If there is a `y` in `f`'s domain with `c = ArchimedeanClass (y - x)`, but there
is no closer `z` to `x` where the difference is of a higher `ArchimedeanClass`, 
then
`f.eval x` is simply `f.val y` truncated at `c`.

This doesn't mean every `x` can be evaluated this way: it is possible that one c
an find
an infinite chain of `y` that keeps getting closer to `x` in terms of Archimedea
n classes,
yet `x` is still isolated within a very high Archimedean class. In fact, in the 
next theorem,
we will show that there is always such chain for `x` not in `f`'s domain.
-/
theorem eval_eq_truncLT [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    {c : FiniteArchimedeanClass M} {y : f.val.domain}
    (hy : ArchimedeanClass.mk (y.val - x) = c.val) (h : ∀ z : f.val.domain, z.val - x ∉ ball K c) :
    f.eval x = toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.val y))) := by
  unfold eval
  rw [toLex.injective.eq_iff]
  ext d
  simp only
  obtain hd | hd := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hd]
    exact evalCoeff_eq _ fun _ ↦ by simpa [hy]
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hd]
    apply evalCoeff_eq_zero
    contrapose! h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, (ball_strictAnti K).antitone (by simpa using hd) hz⟩

/-- For `x` not in `f`'s domain, there is an infinite chain of `y` from `f`'s domain
that keeps getting closer to `x` in terms of Archimedean classes. -/
/-
**HahnEmbedding.Partial.exists_sub_mem_ball** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbed
ding.Partial`。
形式化陈述：exists_sub_mem_ball [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x
 ∉ f.val.domain) (y : f.val.domain) : exists z : f.val.domain, z.val - x in ball
 K (mk _ (val_sub_ne_zero f hx y))
参数：hx : x ∉ f.val.domain；y : f.val.domain。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Partial.val_sub_ne_zero`：val_sub_ne_zero {x : M} (hx : x ∉
 f.val.domain) (y : f.val.domain) : y.val - x != 0
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `HahnEmbedding.Partial.eval_eq_truncLT`：eval_eq_truncLT [IsOrderedAddMono
id R] [Archimedean R] {x : M} {c : FiniteArchimedeanClass M} {y : f.val.domain} 
(hy : ArchimedeanClass.mk (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `HahnEmbedding.IsPartial.truncLT_mem_range`：∀ {K : Type u_1} [inst : Divi
sionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archim
edean K]   {M : Type u_2} [inst…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `HahnEmbedding.Partial.eval_ne`：eval_ne [IsOrderedAddMonoid R] [Archimede
an R] {x : M} (hx : x ∉ f.val.domain) (y : f.val.domain) : f.eval x != f.val y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
For `x` not in `f`'s domain, there is an infinite chain of `y` from `f`'s domain
that keeps getting closer to `x` in terms of Archimedean classes.
-/
theorem exists_sub_mem_ball [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) :
    ∃ z : f.val.domain, z.val - x ∈ ball K (mk _ (val_sub_ne_zero f hx y)) := by
  set c := mk _ (val_sub_ne_zero f hx y)
  have hc : ArchimedeanClass.mk (y.val - x) = c := rfl
  by_contra!; apply hx
  have h := f.eval_eq_truncLT hc this
  obtain ⟨x', hx'⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range y c)
  rw [← hx'] at h
  contrapose! h
  exact f.eval_ne h _

/-- For `x` not in `f`'s domain, `f.eval x` is consistent with `f`'s monotonicity. -/
/-
**HahnEmbedding.Partial.eval_lt** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.Partial
`。
形式化陈述：eval_lt [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.dom
ain) (y : f.val.domain) (h : x < y.val) : f.eval x < f.val y
参数：hx : x ∉ f.val.domain；y : f.val.domain；h : x < y.val。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnSeries.lt_iff`：lt_iff (a b : Lex R⟦Γ⟧) : a < b ↔ exists (i : Γ), (fo
rall (j : Γ), j < i -> (ofLex a).coeff j = (ofLex b).coeff j) ∧ (ofLex a).coeff 
i < (of…
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `HahnEmbedding.Partial.evalCoeff_eq`：evalCoeff_eq [IsOrderedAddMonoid R] 
[Archimedean R] {x : M} {c : FiniteArchimedeanClass M} {y : f.val.domain} (hy : 
y.val - x in ball K c) :…
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `HahnEmbedding.Partial.val_sub_ne_zero`：val_sub_ne_zero {x : M} (hx : x ∉
 f.val.domain) (y : f.val.domain) : y.val - x != 0
· 使用定理 `HahnEmbedding.Partial.exists_sub_mem_ball`：exists_sub_mem_ball [IsOrdere
dAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) (y : f.val.domain)
 : exists z : f.val.domain, z.v…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_lt_sub_iff_right`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α]
 [AddRightStrictMono α] {a b : α} (c : α), a - c < b - c ↔ a < b
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg`：∀ {M : Type u_1} [inst : AddC
ommGroup M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M}, 
  ArchimedeanClass.mk a < Archi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `_private.Mathlib.Algebra.Order.Module.HahnEmbedding.0.HahnEmbedding.Part
ial.eval_lt._abel_1_5`：∀ {K : Type u_2} [inst : DivisionRing K] [inst_1 : Linear
Order K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean K]   {M : Type u_1} [i
nst…
· 使用定理 `ArchimedeanClass.mk_sub_comm`：∀ {M : Type u_1} [inst : AddCommGroup M] [
inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] (a b : M),   Archimedean
Class.mk (a - b) =…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ArchimedeanClass.mk_add_eq_mk_left`：∀ {M : Type u_1} [inst : AddCommGrou
p M] [inst_1 : LinearOrder M] [inst_2 : IsOrderedAddMonoid M] {a b : M},   Archi
medeanClass.mk a < Archi…
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `HahnEmbedding.IsPartial.strictMono`：∀ {K : Type u_1} [inst : DivisionRin
g K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean K
]   {M : Type u_2} [inst…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
For `x` not in `f`'s domain, `f.eval x` is consistent with `f`'s monotonicity.
-/
theorem eval_lt [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) (h : x < y.val) : f.eval x < f.val y := by
  -- Expand the definition of `HahnSeries`' order. We need to find the first coefficient that
  -- dictates the < relation. This coefficient is exactly at the Archimedean class of `y - x`
  rw [HahnSeries.lt_iff]
  have hxy0 : y.val - x ≠ 0 := sub_ne_zero_of_ne h.ne.symm
  refine ⟨mk (y.val - x) hxy0, ?_, ?_⟩
  · -- All coefficients before the dictating term are the same
    intro j hj
    apply evalCoeff_eq
    simpa [j.prop] using! fun _ ↦ hj
  -- Show the dictating coefficient
  suffices f.evalCoeff x (mk (y.val - x) hxy0) < (ofLex (f.val y)).coeff (mk _ hxy0) by
    simpa [eval] using! this
  -- We find `z` from `f`'s domain to approximate `x`. Such approximation obeys:
  -- * `f.eval x = f.val z`
  -- * `x < y → z < y`
  -- * `mk (x - y) = mk (z - y)`
  obtain ⟨z, hz⟩ := f.exists_sub_mem_ball hx y
  rw [f.evalCoeff_eq hz]
  have : z ≠ x := by rintro rfl; exact hx z.2
  have hzy : z < y := by
    change z.val < y.val
    refine (sub_lt_sub_iff_right x).mp <|
      ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg ?_ (sub_nonneg_of_le h.le)
    simpa using! hz (by simpa [sub_eq_zero])
  have hzyne : z.val - y.val ≠ 0 := by
    apply sub_ne_zero_of_ne
    simpa using! hzy.ne
  have hzyclass : mk (y.val - x) hxy0 = mk (z.val - y.val) hzyne := by
    suffices ArchimedeanClass.mk (y.val - x) = .mk (z.val - y.val) by
      simpa [Subtype.ext_iff] using! this
    have : y.val - z.val = y.val - x + (x - z.val) := by abel
    rw [ArchimedeanClass.mk_sub_comm z.val y.val, this]
    refine (ArchimedeanClass.mk_add_eq_mk_left ?_).symm
    rw [ArchimedeanClass.mk_sub_comm x z.val]
    simpa using! hz (by simpa [sub_eq_zero])
  -- Since both `y` and `z` are in the domain, we can apply `f`'s monotonicity on them
  rw [← f.prop.strictMono.lt_iff_lt, HahnSeries.lt_iff] at hzy
  obtain ⟨i, hj, hi⟩ := hzy
  -- We show that the dictating coefficient of `f.val y < f.val z`
  -- is at the same position as the dictating coefficient of `f.eval x < f.val y`
  have hieq : i = mk (y.val - x) hxy0 := by
    apply le_antisymm
    · by_contra! hlt
      obtain hj := sub_eq_zero_of_eq (hj (mk _ hxy0) hlt)
      contrapose! hj
      rw [← HahnSeries.coeff_sub, ← ofLex_sub, ← LinearPMap.map_sub, hzyclass]
      apply f.coeff_ne_zero
    · contrapose! hi
      rw [hzyclass] at hi
      have hzy : z.val - y.val ∈ ball K i := fun _ ↦ hi
      exact (f.coeff_eq_of_mem y.val (by simp) hzy (by simp)).le
  exact hieq ▸ hi

/-- Extend `f` to a larger partial linear map by adding a new `x`. -/
noncomputable
/-
**HahnEmbedding.Partial.extendFun** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbedding.Parti
al`。
形式化陈述：extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.d
omain) : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧
参数：hx : x ∉ f.val.domain。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) :
    M →ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ :=
  .supSpanSingleton f.val x (eval f x) hx
/-
**HahnEmbedding.Partial.extendFun_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbe
dding.Partial`。
形式化陈述：extendFun_strictMono [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : 
x ∉ f.val.domain) : StrictMono (f.extendFun hx)
参数：hx : x ∉ f.val.domain。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `lt_of_sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, 0 < a - b → b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `Lex.instIsRightCancelAdd`：∀ {α : Type u_1} [inst : Add α] [IsRightCancel
Add α], IsRightCancelAdd (Lex α)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.map_sub`：map_sub (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x -
 y) = f x - f y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `LinearPMap.domain_supSpanSingleton`：domain_supSpanSingleton (f : E ->ₛₗ.
[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) : (f.supSpanSingleton x y hx).domain 
= f.domain ⊔ K ∙ x
· 使用定理 `HahnEmbedding.Partial.extendFun.eq_1`：∀ {K : Type u_1} [inst : DivisionR
ing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean
 K]   {M : Type u_2} [inst…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `AddMemClass.isRightCancelAdd`：∀ {M : Type u_1} {A : Type u_3} [inst : Ad
d M] [inst_1 : SetLike A M] [hA : AddMemClass A M] [IsRightCancelAdd M]   (S : A
), IsRightCancelAd…
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 47 条，此处仅展示前 30 条）
-/
theorem extendFun_strictMono [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : StrictMono (f.extendFun hx) := by
  have hx' {c : K} (hc : c ≠ 0) : -c • x ∉ f.val.domain := by
    contrapose hx
    rwa [neg_smul, neg_mem_iff, Submodule.smul_mem_iff _ hc] at hx
  -- only need to prove `0 < f v` for `0 < v = z - y`
  intro y z hyz
  rw [← sub_pos] at hyz
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyzmem := (z - y).prop
  nth_rw 1 [extendFun, LinearPMap.domain_supSpanSingleton] at hyzmem
  -- decompose `v = a + c • x`, reducing this to eval_lt
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hyzmem
  have : z - y = ⟨a + b, hab.symm ▸ (z - y).prop⟩ := by simp_rw [hab]
  rw [this] at ⊢ hyz
  have habpos : 0 < a + b := by exact hyz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
  rw [← hc] at habpos
  simp_rw [← hc, extendFun]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ hx _ ha]
  suffices f.eval (-c • x) < f.val ⟨a, ha⟩ by
    rw [eval_smul, neg_smul] at this
    exact neg_lt_iff_pos_add.mp this
  have hac : -c • x < a := by
    rw [neg_smul]
    exact neg_lt_iff_pos_add.mpr habpos
  by_cases hc : c = 0
  · rw [hc] at ⊢ hac
    suffices f.val 0 < f.val ⟨a, ha⟩ by simpa using! this
    exact f.prop.strictMono (by simpa using! hac)
  · exact f.eval_lt (hx' hc) ⟨a, ha⟩ hac
/-
**HahnEmbedding.Partial.baseEmbedding_le_extendFun** 是 Mathlib 中的一个定理，位于命名空间 `Ha
hnEmbedding.Partial`。
形式化陈述：baseEmbedding_le_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M} 
(hx : x ∉ f.val.domain) : seed.baseEmbedding <= f.extendFun hx
参数：hx : x ∉ f.val.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnEmbedding.Partial.extendFun.eq_1`：∀ {K : Type u_1} [inst : DivisionR
ing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean
 K]   {M : Type u_2} [inst…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `HahnEmbedding.IsPartial.baseEmbedding_le`：∀ {K : Type u_1} [inst : Divis
ionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archime
dean K]   {M : Type u_2} [inst…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `LinearPMap.left_le_sup`：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] 
[inst_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst
_3 : _root_.…
-/
theorem baseEmbedding_le_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : seed.baseEmbedding ≤ f.extendFun hx := by
  rw [extendFun]
  exact le_trans f.prop.baseEmbedding_le <| LinearPMap.left_le_sup _ _ _
/-
**HahnEmbedding.Partial.truncLT_eval_mem_range_extendFun** 是 Mathlib 中的一个定理，位于命名
空间 `HahnEmbedding.Partial`。
形式化陈述：truncLT_eval_mem_range_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x
 : M} (hx : x ∉ f.val.domain) (c : FiniteArchimedeanClass M) : toLex (HahnSeries
.truncLTLinearMap K c (ofLex (f.eval x))) in LinearMap.range (f.extendFun hx).to
Fun
参数：hx : x ∉ f.val.domain；c : FiniteArchimedeanClass M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HahnEmbedding.Partial.extendFun.eq_1`：∀ {K : Type u_1} [inst : DivisionR
ing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean
 K]   {M : Type u_2} [inst…
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `HahnEmbedding.IsPartial.truncLT_mem_range`：∀ {K : Type u_1} [inst : Divi
sionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archim
edean K]   {M : Type u_2} [inst…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
· 使用定理 `LinearPMap.toFun_eq_coe`：toFun_eq_coe (f : E ->ₛₗ.[σ] F) (x : f.domain) 
: f.toFun x = f x
· 使用定理 `LinearPMap.supSpanSingleton_apply_mk_of_mem`：supSpanSingleton_apply_mk_o
f_mem (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain) {x' : E} (hx' : (x'
 : E) in f.domain) : f.supSpanSin…
· 使用定理 `toLex_inj`：toLex_inj {a b : α} : toLex a = toLex b ↔ a = b
· 使用定理 `HahnSeries.ext`：∀ {Γ : Type u_1} {R : Type u_2} {inst : PartialOrder Γ} 
{inst_1 : Zero R} {x y : HahnSeries Γ R},   x.coeff = y.coeff → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `HahnSeries.coe_truncLTLinearMap`：coe_truncLTLinearMap [DecidableLT Γ] (c
 : Γ) : (truncLTLinearMap R c : V⟦Γ⟧ -> V⟦Γ⟧) = truncLT c
· 使用定理 `HahnSeries.coeff_truncLT_of_lt`：coeff_truncLT_of_lt [PartialOrder Γ] [De
cidableLT Γ] {c i : Γ} (h : i < c) (x : R⟦Γ⟧) : (truncLT c x).coeff i = x.coeff 
i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnEmbedding.Partial.evalCoeff_eq`：evalCoeff_eq [IsOrderedAddMonoid R] 
[Archimedean R] {x : M} {c : FiniteArchimedeanClass M} {y : f.val.domain} (hy : 
y.val - x in ball K c) :…
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `FiniteArchimedeanClass.ball_strictAnti`：ball_strictAnti : StrictAnti (ba
ll (M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HahnSeries.coeff_truncLT_of_le`：coeff_truncLT_of_le [LinearOrder Γ] {c i
 : Γ} (h : c <= i) (x : R⟦Γ⟧) : (truncLT c x).coeff i = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
（共 38 条，此处仅展示前 30 条）
-/
theorem truncLT_eval_mem_range_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.eval x))) ∈
    LinearMap.range (f.extendFun hx).toFun := by
  rw [extendFun, LinearMap.mem_range]
  by_cases h : ∃ y : f.val.domain, y.val - x ∈ ball K c
  · -- if `x` is not isolated within `c`, the truncation at `c` equals to truncating
    -- a nearby `y` in the domain
    obtain ⟨y, hy⟩ := h
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range y c)
    refine ⟨⟨z.val, by simpa using Submodule.mem_sup_left z.prop⟩, ?_⟩
    rw [LinearPMap.toFun_eq_coe] at hz
    rw [LinearPMap.toFun_eq_coe, LinearPMap.supSpanSingleton_apply_mk_of_mem _ _ _ z.prop]
    rw [hz, toLex_inj]
    ext d
    obtain hdc | hdc := lt_or_ge d c
    · simp_rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc]
      refine (f.evalCoeff_eq (Set.mem_of_mem_of_subset hy ?_)).symm
      simpa using (ball_strictAnti K hdc).le
    · simp_rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hdc]
  · -- if `x` is isolated within c, truncating has no effect because the trailing coefficients
    -- are already 0
    refine ⟨⟨x, by simpa using Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)⟩, ?_⟩
    apply_fun ofLex
    rw [ofLex_toLex, LinearPMap.toFun_eq_coe, LinearPMap.supSpanSingleton_apply_self]
    ext d
    obtain hdc | hdc := lt_or_ge d c
    · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc]
    rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hdc, eval, ofLex_toLex]
    apply f.evalCoeff_eq_zero
    contrapose h
    obtain ⟨y, hy⟩ := h
    exact ⟨y, Set.mem_of_mem_of_subset hy (by simpa using (ball_strictAnti K).antitone hdc)⟩
/-
**HahnEmbedding.Partial.truncLT_mem_range_extendFun** 是 Mathlib 中的一个定理，位于命名空间 `H
ahnEmbedding.Partial`。
形式化陈述：truncLT_mem_range_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
 (hx : x ∉ f.val.domain) (y : (f.extendFun hx).domain) (c : FiniteArchimedeanCla
ss M) : toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.extendFun hx y))) in Li
nearMap.range (f.extendFun hx).toFun
参数：hx : x ∉ f.val.domain；y : (f.extendFun hx).domain；c : FiniteArchimedeanClass 
M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.domain_supSpanSingleton`：domain_supSpanSingleton (f : E ->ₛₗ.
[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) : (f.supSpanSingleton x y hx).domain 
= f.domain ⊔ K ∙ x
· 使用定理 `HahnEmbedding.Partial.extendFun.eq_1`：∀ {K : Type u_1} [inst : DivisionR
ing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean
 K]   {M : Type u_2} [inst…
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearPMap.supSpanSingleton_apply_mk`：supSpanSingleton_apply_mk (f : E -
>ₛₗ.[σ] F) (x : E) (y : F) (hx : x ∉ f.domain) (x' : E) (hx' : x' in f.domain) (
c : K) : f.supSpanSingleto…
· 使用定理 `ofLex_add`：∀ {α : Type u_1} [inst : Add α] (a b : Lex α), ofLex (a + b) 
= ofLex a + ofLex b
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `toLex_add`：∀ {α : Type u_1} [inst : Add α] (a b : α), toLex (a + b) = to
Lex a + toLex b
· 使用定理 `ofLex_smul`：∀ {β : Type u_2} {α : Type u_1} [inst : SMul β α] (b : β) (a
 : Lex α), ofLex (b • a) = b • ofLex a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `toLex_smul`：∀ {β : Type u_2} {α : Type u_1} [inst : SMul β α] (b : β) (a
 : α), toLex (b • a) = b • toLex a
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `HahnEmbedding.IsPartial.truncLT_mem_range`：∀ {K : Type u_1} [inst : Divi
sionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archim
edean K]   {M : Type u_2} [inst…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
· 使用定理 `LinearPMap.supSpanSingleton_apply_mk_of_mem`：supSpanSingleton_apply_mk_o
f_mem (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain) {x' : E} (hx' : (x'
 : E) in f.domain) : f.supSpanSin…
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `HahnEmbedding.Partial.truncLT_eval_mem_range_extendFun`：truncLT_eval_mem
_range_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.
domain) (c : FiniteArchimedeanClass M) : toL…
-/
theorem truncLT_mem_range_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) (y : (f.extendFun hx).domain) (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.extendFun hx y))) ∈
    LinearMap.range (f.extendFun hx).toFun := by
  obtain ⟨y', hy'⟩ := y
  rw [extendFun, LinearPMap.domain_supSpanSingleton] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hb
  simp_rw [extendFun, ← hab, ← hk]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ ha]
  rw [ofLex_add, map_add, toLex_add, ofLex_smul, map_smul, toLex_smul]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · obtain ⟨⟨a', ha'mem⟩, ha'⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range ⟨a, ha⟩ c)
    refine LinearMap.mem_range.mpr ⟨⟨a', by simpa using Submodule.mem_sup_left ha'mem⟩, ?_⟩
    rw [← ha']
    exact LinearPMap.supSpanSingleton_apply_mk_of_mem f.val _ hx ha'mem
  · apply truncLT_eval_mem_range_extendFun
/-
**HahnEmbedding.Partial.isPartial_extendFun** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbed
ding.Partial`。
形式化陈述：isPartial_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x
 ∉ f.val.domain) : IsPartial seed (extendFun f hx) where strictMono
参数：hx : x ∉ f.val.domain。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Partial.extendFun_strictMono`：extendFun_strictMono [IsOrde
redAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) : StrictMono (f.
extendFun hx)
· 使用定理 `HahnEmbedding.Partial.baseEmbedding_le_extendFun`：baseEmbedding_le_exten
dFun [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) : se
ed.baseEmbedding <= f.extendFun hx
· 使用定理 `HahnEmbedding.Partial.truncLT_mem_range_extendFun`：truncLT_mem_range_ext
endFun [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) (y
 : (f.extendFun hx).domain) (c : Finite…
-/
theorem isPartial_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : IsPartial seed (extendFun f hx) where
  strictMono := f.extendFun_strictMono hx
  baseEmbedding_le := f.baseEmbedding_le_extendFun hx
  truncLT_mem_range := f.truncLT_mem_range_extendFun hx

/-- Promote `HahnEmbedding.Partial.extendFun` to a new `HahnEmbedding.Partial`. -/
noncomputable
/-
**HahnEmbedding.Partial.extend** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbedding.Partial`
。
形式化陈述：extend [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.doma
in) : Partial seed
参数：hx : x ∉ f.val.domain。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Partial.isPartial_extendFun`：isPartial_extendFun [IsOrdere
dAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) : IsPartial seed (
extendFun f hx) where strictMon…
-/
def extend [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) :
    Partial seed := ⟨f.extendFun hx, f.isPartial_extendFun hx⟩
/-
**HahnEmbedding.Partial.lt_extend** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.Parti
al`。
形式化陈述：lt_extend [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.d
omain) : f < f.extend hx
参数：hx : x ∉ f.val.domain。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `LinearPMap.left_le_sup`：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] 
[inst_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst
_3 : _root_.…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem lt_extend [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) :
    f < f.extend hx := by
  apply lt_of_le_of_ne
  · change f.val ≤ (f.extend hx).val
    simpa [extend, extendFun] using! LinearPMap.left_le_sup _ _ _
  by_contra!
  have : f.val.domain = (f.extend hx).val.domain := by congr
  rw [this] at hx
  contrapose! hx with h
  simpa using! Submodule.mem_sup_right (by simp)

/-! ### Step 4: use Zorn's lemma

We show that `sSup` makes sense on `HahnEmbedding.Partial`, which allows us to use Zorn's lemma
to assert the existence of maximal embedding. Since we already show that we can create greater
embeddings by adding new elements, the maximal embedding must have the maximal domain.
-/

/-- A partial linear map that contains every element in a directed set of
`HahnEmbedding.Partial`. -/
noncomputable
/-
**HahnEmbedding.Partial.sSupFun** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbedding.Partial
`。
形式化陈述：sSupFun {c : Set (Partial seed)} (hc : DirectedOn (· <= ·) c) : M ->ₗ.[K] 
Lex R⟦FiniteArchimedeanClass M⟧
参数：Partial seed；hc : DirectedOn (· <= ·) c。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def sSupFun {c : Set (Partial seed)} (hc : DirectedOn (· ≤ ·) c) :
    M →ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ :=
  LinearPMap.sSup ((·.val) '' c) (hc.mono_comp (by simp))
/-
**HahnEmbedding.Partial.sSupFun_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedd
ing.Partial`。
形式化陈述：sSupFun_strictMono [IsOrderedAddMonoid R] {c : Set (Partial seed)} (hnonem
pty : c.Nonempty) (hc : DirectedOn (· <= ·) c) : StrictMono (sSupFun hc)
参数：Partial seed；hnonempty : c.Nonempty；hc : DirectedOn (· <= ·) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRi
ghtStrictMono α] {a b : α}, 0 < a - b → b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `Lex.instIsRightCancelAdd`：∀ {α : Type u_1} [inst : Add α] [IsRightCancel
Add α], IsRightCancelAdd (Lex α)
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `HahnSeries.instIsOrderedAddMonoidLex`：∀ {Γ : Type u_1} {R : Type u_2} [i
nst : LinearOrder Γ] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid R]   [Add
LeftStrictMono R], IsOrder…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.map_sub`：map_sub (f : E ->ₛₗ.[σ] F) (x y : f.domain) : f (x -
 y) = f x - f y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DirectedOn.mono_comp`：DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β 
-> β -> Prop} {g : α -> β} {s : Set α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g 
y)) (hf : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearPMap.mem_domain_sSup_iff`：mem_domain_sSup_iff {c : Set (E ->ₛₗ.[σ]
 F)} (hnonempty : c.Nonempty) (hc : DirectedOn (· <= ·) c) {x : E} : x in (Linea
rPMap.sSup c hc).dom…
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `LinearPMap.sSup_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [
inst_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_
3 : _root_.…
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `HahnEmbedding.IsPartial.strictMono`：∀ {K : Type u_1} [inst : DivisionRin
g K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean K
]   {M : Type u_2} [inst…
· 使用定理 `LinearPMap.map_zero`：map_zero (f : E ->ₛₗ.[σ] F) : f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.coe_lt_coe`：coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) < y ↔ x < y
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
（共 34 条，此处仅展示前 30 条）
-/
theorem sSupFun_strictMono [IsOrderedAddMonoid R] {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) : StrictMono (sSupFun hc) := by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyx := (y - x).prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hyx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hyx
  have : (sSupFun hc) (y - x) = f ⟨(y - x).val, hf⟩ :=
    LinearPMap.sSup_apply _ hmem ⟨(y - x).val, hf⟩
  rw [this]
  obtain ⟨f', _, hf'⟩ := (Set.mem_image _ _ _).mp hmem
  have hmono : StrictMono f := hf'.symm ▸ f'.prop.strictMono
  rw [show 0 = f 0 by simp]
  apply hmono
  rw [← Subtype.coe_lt_coe]
  simp [h]
/-
**HahnEmbedding.Partial.le_sSupFun** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.Part
ial`。
形式化陈述：le_sSupFun {c : Set (Partial seed)} (hc : DirectedOn (· <= ·) c) {f : Part
ial seed} (hf : f in c) : f.val <= sSupFun hc
参数：Partial seed；hc : DirectedOn (· <= ·) c；hf : f in c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.le_sSup`：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [ins
t_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_3 :
 _root_.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem le_sSupFun {c : Set (Partial seed)} (hc : DirectedOn (· ≤ ·) c)
    {f : Partial seed} (hf : f ∈ c) :
    f.val ≤ sSupFun hc :=
  LinearPMap.le_sSup _ <| (Set.mem_image _ _ _).mpr ⟨f, hf, rfl⟩
/-
**HahnEmbedding.Partial.baseEmbedding_le_sSupFun** 是 Mathlib 中的一个定理，位于命名空间 `Hahn
Embedding.Partial`。
形式化陈述：baseEmbedding_le_sSupFun {c : Set (Partial seed)} (hnonempty : c.Nonempty)
 (hc : DirectedOn (· <= ·) c) : seed.baseEmbedding <= sSupFun hc
参数：Partial seed；hnonempty : c.Nonempty；hc : DirectedOn (· <= ·) c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `HahnEmbedding.IsPartial.baseEmbedding_le`：∀ {K : Type u_1} [inst : Divis
ionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archime
dean K]   {M : Type u_2} [inst…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `HahnEmbedding.Partial.le_sSupFun`：le_sSupFun {c : Set (Partial seed)} (h
c : DirectedOn (· <= ·) c) {f : Partial seed} (hf : f in c) : f.val <= sSupFun h
c
-/
theorem baseEmbedding_le_sSupFun {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) : seed.baseEmbedding ≤ sSupFun hc := by
  obtain ⟨f, hf⟩ := hnonempty
  exact le_trans f.prop.baseEmbedding_le (le_sSupFun hc hf)
/-
**HahnEmbedding.Partial.truncLT_mem_range_sSupFun** 是 Mathlib 中的一个定理，位于命名空间 `Hah
nEmbedding.Partial`。
形式化陈述：truncLT_mem_range_sSupFun {c : Set (Partial seed)} (hnonempty : c.Nonempty
) (hc : DirectedOn (· <= ·) c) (x : (sSupFun hc).domain) (c : FiniteArchimedeanC
lass M) : toLex ((HahnSeries.truncLTLinearMap K c) (ofLex (sSupFun hc x))) in Li
nearMap.range (sSupFun hc).toFun
参数：Partial seed；hnonempty : c.Nonempty；hc : DirectedOn (· <= ·) c；x : (sSupFun h
c).domain；c : FiniteArchimedeanClass M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DirectedOn.mono_comp`：DirectedOn.mono_comp {r : α -> α -> Prop} {rb : β 
-> β -> Prop} {g : α -> β} {s : Set α} (hg : forall ⦃x y⦄, r x y -> rb (g x) (g 
y)) (hf : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearPMap.mem_domain_sSup_iff`：mem_domain_sSup_iff {c : Set (E ->ₛₗ.[σ]
 F)} (hnonempty : c.Nonempty) (hc : DirectedOn (· <= ·) c) {x : E} : x in (Linea
rPMap.sSup c hc).dom…
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `HahnEmbedding.IsPartial.truncLT_mem_range`：∀ {K : Type u_1} [inst : Divi
sionRing K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archim
edean K]   {M : Type u_2} [inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `HahnEmbedding.Partial.le_sSupFun`：le_sSupFun {c : Set (Partial seed)} (h
c : DirectedOn (· <= ·) c) {f : Partial seed} (hf : f in c) : f.val <= sSupFun h
c
· 使用定理 `LinearPMap.sSup_apply`：∀ {R : Type u_1} {S : Type u_2} [inst : Ring R] [
inst_1 : Ring S] {σ : R →+* S} {E : Type u_4} [inst_2 : AddCommGroup E]   [inst_
3 : _root_.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `HahnSeries.coe_truncLTLinearMap`：coe_truncLTLinearMap [DecidableLT Γ] (c
 : Γ) : (truncLTLinearMap R c : V⟦Γ⟧ -> V⟦Γ⟧) = truncLT c
-/
theorem truncLT_mem_range_sSupFun {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) (x : (sSupFun hc).domain)
    (c : FiniteArchimedeanClass M) :
    toLex ((HahnSeries.truncLTLinearMap K c) (ofLex (sSupFun hc x))) ∈
    LinearMap.range (sSupFun hc).toFun := by
  obtain hx := x.prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hx
  obtain ⟨f', hmem', hf'⟩ := (Set.mem_image _ _ _).mp hmem
  obtain h := (hf'.symm ▸ f'.prop.truncLT_mem_range) ⟨x, hf⟩ c
  simp_rw [LinearMap.mem_range, LinearPMap.toFun_eq_coe] at ⊢ h
  obtain ⟨x', hx'⟩ := h
  have hmem' : x'.val ∈ (sSupFun hc).domain := by
    apply Set.mem_of_mem_of_subset x'.prop
    exact hf'.symm ▸ (le_sSupFun hc hmem').1
  refine ⟨⟨x'.val, hmem'⟩, ?_⟩
  have hleft : sSupFun hc ⟨x'.val, hmem'⟩ = f x' := LinearPMap.sSup_apply _ hmem _
  have hright : sSupFun hc x = f ⟨x, hf⟩ := LinearPMap.sSup_apply _ hmem ⟨x, hf⟩
  simpa [hleft, hright] using hx'
/-
**HahnEmbedding.Partial.isPartial_sSupFun** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbeddi
ng.Partial`。
形式化陈述：isPartial_sSupFun [IsOrderedAddMonoid R] {c : Set (Partial seed)} (hnonemp
ty : c.Nonempty) (hc : DirectedOn (· <= ·) c) : IsPartial seed (sSupFun hc) wher
e strictMono
参数：Partial seed；hnonempty : c.Nonempty；hc : DirectedOn (· <= ·) c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Partial.sSupFun_strictMono`：sSupFun_strictMono [IsOrderedA
ddMonoid R] {c : Set (Partial seed)} (hnonempty : c.Nonempty) (hc : DirectedOn (
· <= ·) c) : StrictMono (sSupF…
· 使用定理 `HahnEmbedding.Partial.baseEmbedding_le_sSupFun`：baseEmbedding_le_sSupFun
 {c : Set (Partial seed)} (hnonempty : c.Nonempty) (hc : DirectedOn (· <= ·) c) 
: seed.baseEmbedding <= sSupFun hc
· 使用定理 `HahnEmbedding.Partial.truncLT_mem_range_sSupFun`：truncLT_mem_range_sSupF
un {c : Set (Partial seed)} (hnonempty : c.Nonempty) (hc : DirectedOn (· <= ·) c
) (x : (sSupFun hc).domain) (c : Fini…
-/
theorem isPartial_sSupFun [IsOrderedAddMonoid R]
    {c : Set (Partial seed)} (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) :
    IsPartial seed (sSupFun hc) where
  strictMono := sSupFun_strictMono hnonempty hc
  baseEmbedding_le := baseEmbedding_le_sSupFun hnonempty hc
  truncLT_mem_range := truncLT_mem_range_sSupFun hnonempty hc

/-- Promote `HahnEmbedding.Partial.sSupFun` to a `HahnEmbedding.Partial`. -/
noncomputable
/-
**HahnEmbedding.Partial.sSup** 是 Mathlib 中的一个定义，位于命名空间 `HahnEmbedding.Partial`。
形式化陈述：sSup [IsOrderedAddMonoid R] {c : Set (Partial seed)} (hnonempty : c.Nonemp
ty) (hc : DirectedOn (· <= ·) c) : Partial seed
参数：Partial seed；hnonempty : c.Nonempty；hc : DirectedOn (· <= ·) c。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Partial.isPartial_sSupFun`：isPartial_sSupFun [IsOrderedAdd
Monoid R] {c : Set (Partial seed)} (hnonempty : c.Nonempty) (hc : DirectedOn (· 
<= ·) c) : IsPartial seed (sS…
-/
def sSup [IsOrderedAddMonoid R] {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· ≤ ·) c) : Partial seed :=
  ⟨_, isPartial_sSupFun hnonempty hc⟩

variable (seed) in
/-
**HahnEmbedding.Partial.exists_isMax** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbedding.Pa
rtial`。
形式化陈述：exists_isMax [IsOrderedAddMonoid R] : exists f : Partial seed, IsMax f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le_nonempty`：zorn_le_nonempty [Nonempty α] (h : forall c : Set α, I
sChain (· <= ·) c -> c.Nonempty -> BddAbove c) : exists m : α, IsMax m
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsChain.directedOn`：IsChain.directedOn (H : IsChain r s) : DirectedOn r 
s
· 使用定理 `Subtype.instReflLE`：∀ {α : Type u} [inst : LE α] [i : Std.Refl fun x1 x2
 => x1 ≤ x2] {P : α → Prop}, Std.Refl fun x1 x2 => x1 ≤ x2
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `HahnEmbedding.Partial.le_sSupFun`：le_sSupFun {c : Set (Partial seed)} (h
c : DirectedOn (· <= ·) c) {f : Partial seed} (hf : f in c) : f.val <= sSupFun h
c
-/
theorem exists_isMax [IsOrderedAddMonoid R] :
    ∃ f : Partial seed, IsMax f := by
  apply zorn_le_nonempty
  intro c hc hnonempty
  exact ⟨sSup hnonempty hc.directedOn, mem_upperBounds.mpr fun _ hf ↦ le_sSupFun hc.directedOn hf⟩

variable (seed) in
/-- There exists a `HahnEmbedding.Partial` whose domain is the whole module. -/
/-
**HahnEmbedding.Partial.exists_domain_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `HahnEmbe
dding.Partial`。
形式化陈述：exists_domain_eq_top [IsOrderedAddMonoid R] [Archimedean R] : exists f : P
artial seed, f.val.domain = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Partial.exists_isMax`：exists_isMax [IsOrderedAddMonoid R] 
: exists f : Partial seed, IsMax f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HahnEmbedding.Partial.lt_extend`：lt_extend [IsOrderedAddMonoid R] [Archi
medean R] {x : M} (hx : x ∉ f.val.domain) : f < f.extend hx
· 使用定理 `isMax_iff_forall_not_lt`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, I
sMax a ↔ ∀ (b : α), ¬a < b

--- 原说明 ---
There exists a `HahnEmbedding.Partial` whose domain is the whole module.
-/
theorem exists_domain_eq_top [IsOrderedAddMonoid R] [Archimedean R] :
    ∃ f : Partial seed, f.val.domain = ⊤ := by
  obtain ⟨f, hf⟩ := exists_isMax seed
  refine ⟨f, Submodule.eq_top_iff'.mpr ?_⟩
  rw [isMax_iff_forall_not_lt] at hf
  contrapose! hf with hx
  obtain ⟨x, hx⟩ := hx
  exact ⟨f.extend hx, f.lt_extend hx⟩

end Partial

end HahnEmbedding

/-- **Hahn embedding theorem for an ordered module**

There exists a strictly monotone `M →ₗ[K] Lex R⟦FiniteArchimedeanClass M⟧` that maps
`ArchimedeanClass M` to `HahnSeries.orderTop` in the expected way, as long as
`HahnEmbedding.Seed K M R` is nonempty. The `HahnEmbedding.Partial` with maximal domain is the
desired embedding. -/
/-
**hahnEmbedding_isOrderedModule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hahnEmbedding_isOrderedModule [IsOrderedAddMonoid R] [Archimedean R] [h : 
Nonempty (HahnEmbedding.Seed K M R)] : exists f : M ->ₗ[K] Lex R⟦FiniteArchimede
anClass M⟧, StrictMono f ∧ forall (a : M), .mk a = FiniteArchimedeanClass.withTo
pOrderIso M (ofLex (f a)).orderTop
参数：HahnEmbedding.Seed K M R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HahnEmbedding.Partial.exists_domain_eq_top`：exists_domain_eq_top [IsOrde
redAddMonoid R] [Archimedean R] : exists f : Partial seed, f.val.domain = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
· 使用定理 `HahnEmbedding.IsPartial.strictMono`：∀ {K : Type u_1} [inst : DivisionRin
g K] [inst_1 : LinearOrder K] [inst_2 : IsOrderedRing K] [inst_3 : Archimedean K
]   {M : Type u_2} [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HahnEmbedding.Partial.orderTop_eq_archimedeanClassMk`：orderTop_eq_archim
edeanClassMk [IsOrderedAddMonoid R] [Archimedean R] (x : f.val.domain) : FiniteA
rchimedeanClass.withTopOrderIso M (ofLex (…

--- 原说明 ---
**Hahn embedding theorem for an ordered module**

There exists a strictly monotone `M →ₗ[K] Lex R⟦FiniteArchimedeanClass M⟧` that 
maps
`ArchimedeanClass M` to `HahnSeries.orderTop` in the expected way, as long as
`HahnEmbedding.Seed K M R` is nonempty. The `HahnEmbedding.Partial` with maximal
 domain is the
desired embedding.
-/
theorem hahnEmbedding_isOrderedModule [IsOrderedAddMonoid R] [Archimedean R]
    [h : Nonempty (HahnEmbedding.Seed K M R)] :
    ∃ f : M →ₗ[K] Lex R⟦FiniteArchimedeanClass M⟧, StrictMono f ∧
      ∀ (a : M), .mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop := by
  obtain ⟨e, hdomain⟩ := HahnEmbedding.Partial.exists_domain_eq_top h.some
  obtain harch := e.orderTop_eq_archimedeanClassMk
  obtain ⟨⟨fdomain, f⟩, hpartial⟩ := e
  obtain rfl := hdomain
  refine ⟨f ∘ₗ LinearMap.id.codRestrict ⊤ (by simp), ?_, ?_⟩
  · apply hpartial.strictMono.comp
    intro _ _ h
    simpa [← Subtype.coe_lt_coe] using h
  · simp_rw [LinearPMap.mk_apply] at harch
    simp [harch]
