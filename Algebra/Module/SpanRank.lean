/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Xuchun Li, Christian Merten, Jingting Wang, Andrew Yang
-/
module

public import Mathlib.Data.ENat.Lattice
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Minimum Cardinality of generating set of a submodule

In this file, we define the minimum cardinality of a generating set for a submodule, which is
implemented as `spanFinrank` and `spanRank`.
`spanFinrank` takes value in `ℕ` and equals `0` when no finite generating set exists.
`spanRank` takes value as a cardinal.

## Main Definitions

* `spanFinrank`: The minimum cardinality of a generating set of a submodule as a natural
  number. If no finite generating set exists, it is defined to be `0`.
* `spanRank`: The minimum cardinality of a generating set of a submodule as a cardinal.
* `FG.generators`: For a finitely generated submodule, get a set of generating elements with minimal
  cardinality.

## Main Results

* `FG.exists_span_set_card_eq_spanFinrank` : Any submodule has a generating set of cardinality equal
  to `spanRank`.

* `rank_eq_spanRank_of_free` : For a ring `R` (not necessarily commutative) satisfying
  `StrongRankCondition R`, if `M` is a free `R`-module, then the `spanRank` of `M` equals to the
  rank of M.

* `rank_le_spanRank` : For a ring `R` (not necessarily commutative) satisfying
  `StrongRankCondition R`, if `M` is an `R`-module, then the `spanRank` of `M` is less than or equal
  to the rank of M.

## Tags
submodule, generating subset, span rank

## Remark
Note that the corresponding API - `Module.rank` is only defined for a module rather than a
submodule, so there is some asymmetry here. Further refactoring might be needed if this difference
creates a friction later on.
-/

@[expose] public section

namespace Submodule

section Defs

universe u v

variable {R : Type*} {M : Type u} [Semiring R] [AddCommMonoid M] [Module R M]

open Cardinal

/-- The minimum cardinality of a generating set of a submodule as a cardinal. -/
/-
**Submodule.spanRank** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：spanRank (p : Submodule R M) : Cardinal
参数：p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimum cardinality of a generating set of a submodule as a cardinal.
-/
noncomputable def spanRank (p : Submodule R M) : Cardinal := ⨅ (s : {s : Set M // span R s = p}), #s

/-- The minimum cardinality of a generating set of a submodule as a natural number. If no finite
  generating set exists, the span rank is defined to be `0`. -/
/-
**Submodule.spanFinrank** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：spanFinrank (p : Submodule R M) : Nat
参数：p : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The minimum cardinality of a generating set of a submodule as a natural number. 
If no finite
  generating set exists, the span rank is defined to be `0`.
-/
noncomputable def spanFinrank (p : Submodule R M) : ℕ := (spanRank p).toNat
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : Submodule R M) : Nonempty {s : Set M // span R s = p} := ⟨⟨p, by simp⟩⟩
/-
**Submodule.spanRank_toENat_eq_iInf_encard** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`
。
形式化陈述：spanRank_toENat_eq_iInf_encard (p : Submodule R M) : p.spanRank.toENat = (
⨅ (s : Set M) (_ : span R s = p), s.encard)
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.spanRank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M)
, p.spanRank …
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf₂`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {a : α} {f : (i : ι) → κ i → α},   (∀ (i : ι) (j : κ i), a ≤ f…
· 使用定理 `Set.encard.eq_1`：∀ {α : Type u_1} (s : Set α), s.encard = ENat.card ↑s
· 使用定理 `ENat.card.eq_1`：∀ (α : Type u_3), ENat.card α = Cardinal.toENat (Cardina
l.mk α)
· 使用定理 `OrderRingHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : NonAssoc
Semiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3 : Preo
rder β] (sel…
· 使用定理 `ciInf_le'`：ciInf_le' (f : ι -> α) (i : ι) : iInf f <= f i
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toENat_comp_ofENat`：⇑Cardinal.toENat ∘ Cardinal.ofENat = id
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `Submodule.instNonemptySubtypeSetEqSpan`：∀ {R : Type u_1} {M : Type u} [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p :
 Submodule R M), Nonempty { …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Cardinal.ofENat_toENat_le`：ofENat_toENat_le (a : Cardinal) : ↑(toENat a)
 <= a
-/
lemma spanRank_toENat_eq_iInf_encard (p : Submodule R M) : p.spanRank.toENat =
    (⨅ (s : Set M) (_ : span R s = p), s.encard) := by
  rw [spanRank]
  apply le_antisymm
  · refine le_iInf₂ (fun s hs ↦ ?_)
    rw [Set.encard, ENat.card]
    exact toENat.monotone' (ciInf_le' _ (⟨s, hs⟩ : {s : Set M // span R s = p}))
  · have := congrFun toENat_comp_ofENat.{u}.symm (⨅ (s : Set M) (_ : span R s = p), s.encard)
    rw [id_eq] at this; rw [this]
    refine toENat.monotone' (le_ciInf fun s ↦ ?_)
    have : ofENat.{u} (⨅ (s' : Set M), ⨅ (_ : span R s' = p), s'.encard) ≤ ofENat s.1.encard :=
      ofENatHom.monotone' (le_trans (ciInf_le' _ s.1) (ciInf_le' _ s.2))
    apply le_trans this
    rw [Set.encard, ENat.card]
    exact Cardinal.ofENat_toENat_le _
/-
**Submodule.spanRank_toENat_eq_iInf_finset_card** 是 Mathlib 中的一个引理，位于命名空间 `Submo
dule`。
形式化陈述：spanRank_toENat_eq_iInf_finset_card (p : Submodule R M) : p.spanRank.toENa
t = ⨅ (s : {s : Finset M // span R s = p}), (s.1.card : Nat∞)
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.spanRank_toENat_eq_iInf_encard`：spanRank_toENat_eq_iInf_encard
 (p : Submodule R M) : p.spanRank.toENat = (⨅ (s : Set M) (_ : span R s = p), s.
encard)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.encard_ne_top_iff`：encard_ne_top_iff : s.encard != ⊤ ↔ s.Finite
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `iInf₂_le`：∀ {α : Type u_1} {ι : Sort u_4} {κ : ι → Sort u_6} [inst : Com
pleteLattice α] {f : (i : ι) → κ i → α} (i : ι) (j : κ i),   ⨅ i, ⨅ j, f i j ≤…
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Infinite.encard_eq`：∀ {α : Type u_1} {s : Set α}, s.Infinite → s.enc
ard = ⊤
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤
-/
lemma spanRank_toENat_eq_iInf_finset_card (p : Submodule R M) :
    p.spanRank.toENat = ⨅ (s : {s : Finset M // span R s = p}), (s.1.card : ℕ∞) := by
  rw [spanRank_toENat_eq_iInf_encard]
  rcases eq_or_ne (⨅ (s : Set M) (_ : span R s = p), s.encard) ⊤ with (h1 | h2)
  · rw [h1, eq_comm]; simp_rw [iInf_eq_top] at h1 ⊢
    exact fun s ↦ False.elim (Set.encard_ne_top_iff.mpr s.1.finite_toSet (h1 s.1 s.2))
  · simp_rw [← Set.encard_coe_eq_coe_finsetCard]
    apply le_antisymm
    · exact le_iInf fun s ↦ iInf₂_le (s.1 : Set M) s.2
    · refine le_iInf fun s ↦ le_iInf fun h ↦ ?_
      by_cases hs : s.Finite
      · exact iInf_le_of_le ⟨hs.toFinset, by simpa⟩ (by simp)
      · rw [Set.Infinite.encard_eq hs]
        exact OrderTop.le_top _
/-
**Submodule.spanFinrank_eq_iInf** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanFinrank_eq_iInf (p : Submodule R M) : p.spanFinrank = ⨅ (s : {s : Fins
et M // span R s = p}), s.1.card
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.spanRank_toENat_eq_iInf_finset_card`：spanRank_toENat_eq_iInf_f
inset_card (p : Submodule R M) : p.spanRank.toENat = ⨅ (s : {s : Finset M // spa
n R s = p}), (s.1.card : Nat∞)
· 使用引理 `ENat.iInf_toNat`：iInf_toNat : (⨅ i, (f i : Nat∞)).toNat = ⨅ i, f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma spanFinrank_eq_iInf (p : Submodule R M) :
    p.spanFinrank = ⨅ (s : {s : Finset M // span R s = p}), s.1.card := by
  simp [spanFinrank, Cardinal.toNat, spanRank_toENat_eq_iInf_finset_card, ENat.iInf_toNat]

/-- A submodule's `spanRank` is finite if and only if it is finitely generated. -/
@[simp]
/-
**Submodule.spanRank_finite_iff_fg** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_finite_iff_fg {p : Submodule R M} : p.spanRank < aleph0 ↔ p.FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.spanRank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M)
, p.spanRank …
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_coe_eq_restrictScalars`：span_coe_eq_restrictScalars [Semi
ring S] [SMul S R] [Module S M] [IsScalarTower S R M] : span S (p : Set M) = p.r
estrictScalars S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `ciInf_le'`：ciInf_le' (f : ι -> α) (i : ι) : iInf f <= f i

--- 原说明 ---
A submodule's `spanRank` is finite if and only if it is finitely generated.
-/
lemma spanRank_finite_iff_fg {p : Submodule R M} : p.spanRank < aleph0 ↔ p.FG := by
  rw [spanRank, Submodule.fg_def]
  constructor
  · rintro h
    obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s ∈
      Set.range (fun (s : {s : Set M // span R s = p}) ↦ #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
    refine ⟨s.1, ?_, s.2⟩
    simpa [← hs] using h
  · rintro ⟨s, hs₁, hs₂⟩
    exact (ciInf_le' _ ⟨s, hs₂⟩).trans_lt (by simpa)
/-
**Submodule.spanFinrank_of_not_fg** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanFinrank_of_not_fg {p : Submodule R M} (hp : ¬p.FG) : p.spanFinrank = 0
参数：hp : ¬p.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Cardinal.toNat_eq_zero`：toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ <= c
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Submodule.spanRank_finite_iff_fg`：spanRank_finite_iff_fg {p : Submodule 
R M} : p.spanRank < aleph0 ↔ p.FG
-/
lemma spanFinrank_of_not_fg {p : Submodule R M} (hp : ¬p.FG) : p.spanFinrank = 0 := by
  refine toNat_eq_zero.2 ?_
  right
  by_contra! h
  exact hp (spanRank_finite_iff_fg.1 h)

/-- A submodule is finitely generated if and only if its `spanRank` is equal to its `spanFinrank`.
-/
/-
**Submodule.fg_iff_spanRank_eq_spanFinrank** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`
。
形式化陈述：fg_iff_spanRank_eq_spanFinrank {p : Submodule R M} : p.spanRank = p.spanFi
nrank ↔ p.FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.spanFinrank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R
 M), p.spanFinra…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.spanRank_finite_iff_fg`：spanRank_finite_iff_fg {p : Submodule 
R M} : p.spanRank < aleph0 ↔ p.FG
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Cardinal.cast_toNat_eq_iff_lt_aleph0`：cast_toNat_eq_iff_lt_aleph0 {c : C
ardinal} : toNat c = c ↔ c < ℵ₀ where mp h

--- 原说明 ---
A submodule is finitely generated if and only if its `spanRank` is equal to its 
`spanFinrank`.
-/
lemma fg_iff_spanRank_eq_spanFinrank {p : Submodule R M} : p.spanRank = p.spanFinrank ↔ p.FG := by
  rw [spanFinrank, ← spanRank_finite_iff_fg, eq_comm]
  exact cast_toNat_eq_iff_lt_aleph0
/-
**Submodule.FG.spanRank_eq_spanFinrank** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid 
M] [inst_2 : _root_.Module R M]   {p : Submodule R M}, p.FG → p.spanRank = ↑p.sp
anFinrank
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submodule.fg_iff_spanRank_eq_spanFinrank`：fg_iff_spanRank_eq_spanFinrank
 {p : Submodule R M} : p.spanRank = p.spanFinrank ↔ p.FG
-/
lemma FG.spanRank_eq_spanFinrank {p : Submodule R M} (fg : p.FG) : p.spanRank = p.spanFinrank :=
  fg_iff_spanRank_eq_spanFinrank.mpr fg
/-
**Submodule.FG.spanRank_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid 
M] [inst_2 : _root_.Module R M]   {p : Submodule R M}, p.FG → ∀ (n : ℕ), p.spanR
ank ≤ ↑n ↔ p.spanFinrank ≤ n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Cardinal.toNat_le_iff_of_lt_aleph0`：toNat_le_iff_of_lt_aleph0 {a : Cardi
nal.{u}} (n : Nat) (lt : a < Cardinal.aleph0) : a.toNat <= n ↔ a <= n
-/
lemma FG.spanRank_le_iff {p : Submodule R M} (hp : p.FG) (n : ℕ) :
    p.spanRank ≤ n ↔ p.spanFinrank ≤ n :=
  (Cardinal.toNat_le_iff_of_lt_aleph0 n (by simpa)).symm
/-
**Submodule.FG.spanRank_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid 
M] [inst_2 : _root_.Module R M]   {p : Submodule R M}, p.FG → ∀ (n : ℕ), p.spanR
ank = ↑n ↔ p.spanFinrank = n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Cardinal.toNat_eq_iff_of_lt_aleph0`：toNat_eq_iff_of_lt_aleph0 {a : Cardi
nal.{u}} (n : Nat) (lt : a < Cardinal.aleph0) : a.toNat = n ↔ a = n
-/
lemma FG.spanRank_eq_iff {p : Submodule R M} (hp : p.FG) (n : ℕ) :
    p.spanRank = n ↔ p.spanFinrank = n :=
  (Cardinal.toNat_eq_iff_of_lt_aleph0 n (by simpa)).symm
/-
**Submodule.spanRank_span_le_card** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_span_le_card (s : Set M) : (Submodule.span R s).spanRank <= #s
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.spanRank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M)
, p.spanRank …
· 使用定理 `ciInf_le'`：ciInf_le' (f : ι -> α) (i : ι) : iInf f <= f i
-/
lemma spanRank_span_le_card (s : Set M) : (Submodule.span R s).spanRank ≤ #s := by
  rw [spanRank]
  let s' : {s1 : Set M // span R s1 = span R s} := ⟨s, rfl⟩
  exact ciInf_le' _ s'
/-
**Submodule.spanRank_span_range_of_linearIndependent** 是 Mathlib 中的一个引理，位于命名空间 `
Submodule`。
形式化陈述：spanRank_span_range_of_linearIndependent [RankCondition R] {ι : Type u} {v
 : ι -> M} (hv : v.Injective) (hs : LinearIndependent R v) : (span R (.range v))
.spanRank = #ι
参数：hv : v.Injective；hs : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Submodule.spanRank_span_le_card`：spanRank_span_le_card (s : Set M) : (Su
bmodule.span R s).spanRank <= #s
· 使用定理 `Cardinal.mk_range_le`：mk_range_le {α β : Type u} {f : α -> β} : #(range 
f) <= #α
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `Submodule.instNonemptySubtypeSetEqSpan`：∀ {R : Type u_1} {M : Type u} [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p :
 Submodule R M), Nonempty { …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_preimage_of_injective_of_subset_range`：mk_preimage_of_inject
ive_of_subset_range (f : α -> β) (s : Set β) (h : Injective f) (h2 : s subseteq 
range f) : #(f ⁻¹' s) = #s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Cardinal.mk_range_eq`：mk_range_eq (f : α -> β) (h : Injective f) : #(ran
ge f) = #α
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Module.Basis.span_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {v
 : ι → M} (hl…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Module.Basis.le_span`：Module.Basis.le_span {J : Set M} (v : Basis ι R M)
 (hJ : span R J = ⊤) : #(range v) <= #J
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_preimage_eq_inter_range`：image_preimage_eq_inter_range {f : α 
-> β} {t : Set β} : f '' f ⁻¹' t = t inter range f
（共 33 条，此处仅展示前 30 条）
-/
lemma spanRank_span_range_of_linearIndependent [RankCondition R] {ι : Type u} {v : ι → M}
    (hv : v.Injective) (hs : LinearIndependent R v) :
    (span R (.range v)).spanRank = #ι := by
  refine le_antisymm (le_trans (spanRank_span_le_card _) mk_range_le) (le_ciInf fun x ↦ ?_)
  have : #x.1 = #((Subtype.val : span R (.range v) → _) ⁻¹' x.1) :=
    (mk_preimage_of_injective_of_subset_range _ _ Subtype.val_injective (by simp [← x.2])).symm
  rw [this]
  refine le_trans ?_ ((Module.Basis.span hs).le_span (R := R) (J := Subtype.val ⁻¹' x.1) ?_)
  · rw [mk_range_eq]
    exact .of_comp (f := Subtype.val) (by convert! hv; ext; simp [Module.Basis.span_apply])
  · apply map_injective_of_injective (f := (span R _).subtype) (injective_subtype _)
    simp [map_span, Set.image_preimage_eq_inter_range, Set.inter_eq_self_of_subset_left, ← x.2]
/-
**Submodule.spanRank_span_of_linearIndepOn** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`
。
形式化陈述：spanRank_span_of_linearIndepOn [RankCondition R] (s : Set M) (hs : LinearI
ndepOn R id s) : (span R s).spanRank = #s
参数：s : Set M；hs : LinearIndepOn R id s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.spanRank_span_range_of_linearIndependent`：spanRank_span_range_
of_linearIndependent [RankCondition R] {ι : Type u} {v : ι -> M} (hv : v.Injecti
ve) (hs : LinearIndependent R v) : (span…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma spanRank_span_of_linearIndepOn [RankCondition R] (s : Set M) (hs : LinearIndepOn R id s) :
    (span R s).spanRank = #s := by
  simp [← spanRank_span_range_of_linearIndependent Subtype.val_injective hs]
/-
**Submodule.spanFinrank_span_le_encard** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanFinrank_span_le_encard (s : Set M) : (span R s).spanFinrank <= s.encar
d
参数：s : Set M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.spanFinrank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R
 M), p.spanFinra…
· 使用定理 `Set.encard.eq_1`：∀ {α : Type u_1} (s : Set α), s.encard = ENat.card ↑s
· 使用定理 `ENat.card.eq_1`：∀ (α : Type u_3), ENat.card α = Cardinal.toENat (Cardina
l.mk α)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `OrderRingHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : α ->+*o β) : f.toRi
ngHom = f
· 使用定理 `OrderRingHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : NonAssoc
Semiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3 : Preo
rder β] (sel…
· 使用引理 `Submodule.spanRank_span_le_card`：spanRank_span_le_card (s : Set M) : (Su
bmodule.span R s).spanRank <= #s
-/
lemma spanFinrank_span_le_encard (s : Set M) : (span R s).spanFinrank ≤ s.encard := by
  rw [spanFinrank, Set.encard, ENat.card]
  exact le_trans (by simp) (toENat.monotone' (spanRank_span_le_card (R := R) s))
/-
**Submodule.spanFinrank_span_le_ncard_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Submo
dule`。
形式化陈述：spanFinrank_span_le_ncard_of_finite {s : Set M} (hs : s.Finite) : (span R 
s).spanFinrank <= s.ncard
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Submodule.spanFinrank_span_le_encard`：spanFinrank_span_le_encard (s : Se
t M) : (span R s).spanFinrank <= s.encard
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.Finite.cast_ncard_eq`：∀ {α : Type u_1} {s : Set α}, s.Finite → ↑s.nc
ard = s.encard
-/
lemma spanFinrank_span_le_ncard_of_finite {s : Set M} (hs : s.Finite) :
    (span R s).spanFinrank ≤ s.ncard := by
  rw [← Nat.cast_le (α := ℕ∞)]
  exact le_trans (spanFinrank_span_le_encard _) hs.cast_ncard_eq.ge

/-- Constructs a generating set with cardinality equal to the `spanRank` of the submodule -/
/-
**Submodule.exists_span_set_card_eq_spanRank** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：exists_span_set_card_eq_spanRank (p : Submodule R M) : exists s : Set M, #
s = p.spanRank ∧ span R s = p
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.spanRank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M)
, p.spanRank …
· 使用定理 `csInf_mem`：csInf_mem (hs : s.Nonempty) : sInf s in s
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_coe_eq_restrictScalars`：span_coe_eq_restrictScalars [Semi
ring S] [SMul S R] [Module S M] [IsScalarTower S R M] : span S (p : Set M) = p.r
estrictScalars S
· 使用定理 `Submodule.restrictScalars_self`：restrictScalars_self (V : Submodule R M)
 : V.restrictScalars R = V
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
Constructs a generating set with cardinality equal to the `spanRank` of the subm
odule
-/
theorem exists_span_set_card_eq_spanRank (p : Submodule R M) :
    ∃ s : Set M, #s = p.spanRank ∧ span R s = p := by
  rw [spanRank]
  obtain ⟨s, hs⟩ : ⨅ (s : {s : Set M // span R s = p}), #s ∈
    Set.range (fun (s : {s : Set M // span R s = p}) ↦ #s) := csInf_mem ⟨#p, ⟨⟨p, by simp⟩, rfl⟩⟩
  exact ⟨s.1, ⟨hs, s.2⟩⟩

/-- Constructs a generating set with cardinality equal to the `spanFinrank` of the submodule when
  the submodule is finitely generated. -/
/-
**Submodule.FG.exists_span_set_encard_eq_spanFinrank** 是 Mathlib 中的一个定理，位于命名空间 `
Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid 
M] [inst_2 : _root_.Module R M]   {p : Submodule R M}, p.FG → ∃ s, s.encard = ↑p
.spanFinrank ∧ Submodule.span R s = p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submodule.fg_iff_spanRank_eq_spanFinrank`：fg_iff_spanRank_eq_spanFinrank
 {p : Submodule R M} : p.spanRank = p.spanFinrank ↔ p.FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.encard.eq_1`：∀ {α : Type u_1} (s : Set α), s.encard = ENat.card ↑s
· 使用定理 `ENat.card.eq_1`：∀ (α : Type u_3), ENat.card α = Cardinal.toENat (Cardina
l.mk α)
· 使用定理 `Submodule.spanFinrank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R
 M), p.spanFinra…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `Cardinal.toNat_natCast`：∀ (n : ℕ), Cardinal.toNat ↑n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Constructs a generating set with cardinality equal to the `spanFinrank` of the s
ubmodule when
  the submodule is finitely generated.
-/
theorem FG.exists_span_set_encard_eq_spanFinrank {p : Submodule R M} (h : p.FG) :
    ∃ s : Set M, s.encard = p.spanFinrank ∧ span R s = p := by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
  refine ⟨s, ⟨?_, hs₂⟩⟩
  have := fg_iff_spanRank_eq_spanFinrank.mpr h
  rw [Set.encard, ENat.card, spanFinrank, hs₁, this]
  simp

/-- Constructs a generating finset with cardinality equal to the `spanFinrank` of the submodule
  when the submodule is finitely generated. -/
/-
**Submodule.FG.exists_span_finset_card_eq_spanFinrank** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid 
M] [inst_2 : _root_.Module R M]   {p : Submodule R M}, p.FG → ∃ s, s.card = p.sp
anFinrank ∧ Submodule.span R ↑s = p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.FG.exists_span_set_encard_eq_spanFinrank`：∀ {R : Type u_1} {M 
: Type u} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   {p : Submodule R M}, p.FG → ∃ s,…
· 使用定理 `Set.finite_of_encard_eq_coe`：finite_of_encard_eq_coe {k : Nat} (h : s.en
card = k) : s.Finite
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.encard_eq_coe_toFinset_card`：∀ {α : Type u_1} {s : Set α} (h 
: s.Finite), s.encard = ↑h.toFinset.card
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s

--- 原说明 ---
Constructs a generating finset with cardinality equal to the `spanFinrank` of th
e submodule
  when the submodule is finitely generated.
-/
theorem FG.exists_span_finset_card_eq_spanFinrank {p : Submodule R M} (h : p.FG) :
    ∃ s : Finset M, s.card = p.spanFinrank ∧ span R s = p := by
  obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_encard_eq_spanFinrank h
  have s_f := Set.finite_of_encard_eq_coe hs₁
  refine ⟨s_f.toFinset, ⟨?_, by simpa using hs₂⟩⟩
  simpa [s_f.encard_eq_coe_toFinset_card, ENat.natCast_inj] using hs₁
/-
**Submodule.lift_spanRank_le_iff_exists_span_set_card_le** 是 Mathlib 中的一个引理，位于命名
空间 `Submodule`。
形式化陈述：lift_spanRank_le_iff_exists_span_set_card_le (p : Submodule R M) {a : Card
inal.{max u v}} : Cardinal.lift.{v} p.spanRank <= a ↔ exists s : Set M, Cardinal
.lift.{v} #s <= a ∧ span R s = p
参数：p : Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用引理 `Submodule.spanRank_span_le_card`：spanRank_span_le_card (s : Set M) : (Su
bmodule.span R s).spanRank <= #s
-/
lemma lift_spanRank_le_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal.{max u v}} :
    Cardinal.lift.{v} p.spanRank ≤ a ↔ ∃ s : Set M, Cardinal.lift.{v} #s ≤ a ∧ span R s = p := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ := exists_span_set_card_eq_spanRank p
    exact ⟨s, ⟨hs₁ ▸ h, hs₂⟩⟩
  · exact fun ⟨s, ⟨h₁, h₂⟩⟩ ↦ h₂.symm ▸ (Cardinal.lift_le.mpr (spanRank_span_le_card s)).trans h₁

/-- For a finitely generated submodule, its spanRank is less than or equal to a cardinal `a`
  if and only if there is a generating subset with cardinality less than or equal to `a`. -/
/-
**Submodule.FG.spanRank_le_iff_exists_span_set_card_le** 是 Mathlib 中的一个定理，位于命名空间
 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid 
M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {a : Cardinal.{u}}, p.span
Rank ≤ a ↔ ∃ s, Cardinal.mk ↑s ≤ a ∧ Submodule.span R s = p
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Submodule.lift_spanRank_le_iff_exists_span_set_card_le`：lift_spanRank_le
_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal.{max u v}} : Card
inal.lift.{v} p.spanRank <= a ↔ exists s : S…

--- 原说明 ---
For a finitely generated submodule, its spanRank is less than or equal to a card
inal `a`
  if and only if there is a generating subset with cardinality less than or equa
l to `a`.
-/
lemma FG.spanRank_le_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal} :
    p.spanRank ≤ a ↔ ∃ s : Set M, #s ≤ a ∧ span R s = p := by
  convert! lift_spanRank_le_iff_exists_span_set_card_le p (a := a) <;> simp

@[simp]
/-
**Submodule.spanRank_eq_zero_iff_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_eq_zero_iff_eq_bot {I : Submodule R M} : I.spanRank = 0 ↔ I = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.FG.spanRank_le_iff_exists_span_set_card_le`：∀ {R : Type u_1} {
M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modu
le R M]   (p : Submodule R M) {a : Cardina…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.spanRank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M)
, p.spanRank …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Cardinal.iInf_eq_zero_iff`：iInf_eq_zero_iff {ι : Sort*} {f : ι -> Cardin
al} : (⨅ i, f i) = 0 ↔ IsEmpty ι ∨ exists i, f i = 0
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma spanRank_eq_zero_iff_eq_bot {I : Submodule R M} : I.spanRank = 0 ↔ I = ⊥ := by
  constructor
  · intro h
    obtain ⟨s, ⟨hs₁, hs₂⟩⟩ :=
      (FG.spanRank_le_iff_exists_span_set_card_le I (a := 0)).mp (by rw [h])
    simp only [nonpos_iff_eq_zero, mk_eq_zero_iff, Set.isEmpty_coe_sort] at hs₁
    simp_all
  · rintro rfl; rw [spanRank]
    exact Cardinal.iInf_eq_zero_iff.mpr (Or.inr ⟨⟨∅, by simp⟩, by simp⟩)

@[simp]
/-
**Submodule.spanRank_bot** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_bot : (⊥ : Ideal R).spanRank = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submodule.spanRank_eq_zero_iff_eq_bot`：spanRank_eq_zero_iff_eq_bot {I : 
Submodule R M} : I.spanRank = 0 ↔ I = ⊥
-/
lemma spanRank_bot : (⊥ : Ideal R).spanRank = 0 := Submodule.spanRank_eq_zero_iff_eq_bot.mpr rfl

@[simp]
/-
**Submodule.spanFinrank_bot** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanFinrank_bot : (⊥ : Submodule R M).spanFinrank = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
lemma spanFinrank_bot : (⊥ : Submodule R M).spanFinrank = 0 := by simp [spanFinrank]

@[nontriviality]
/-
**Submodule.spanRank_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_subsingleton [Subsingleton R] (p : Submodule R M) : p.spanRank = 
0
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
lemma spanRank_subsingleton [Subsingleton R] (p : Submodule R M) : p.spanRank = 0 := by
  simp [nontriviality]

@[nontriviality]
/-
**Submodule.spanFinrank_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanFinrank_subsingleton [Subsingleton R] (p : Submodule R M) : p.spanFinr
ank = 0
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_bot_of_subsingleton`：eq_bot_of_subsingleton [Subsingleton p
] : p = ⊥
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用引理 `Submodule.spanFinrank_bot`：spanFinrank_bot : (⊥ : Submodule R M).spanFin
rank = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma spanFinrank_subsingleton [Subsingleton R] (p : Submodule R M) : p.spanFinrank = 0 := by
  have := Module.subsingleton R M
  simp [Submodule.eq_bot_of_subsingleton]

/-- Generating elements for the submodule of minimum cardinality. -/
/-
**Submodule.generators** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：generators (p : Submodule R M) : Set M
参数：p : Submodule R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p

--- 原说明 ---
Generating elements for the submodule of minimum cardinality.
-/
noncomputable def generators (p : Submodule R M) : Set M :=
  Classical.choose (exists_span_set_card_eq_spanRank p)
/-
**Submodule.generators_card** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：generators_card (p : Submodule R M) : #(generators p) = spanRank p
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma generators_card (p : Submodule R M) : #(generators p) = spanRank p :=
  (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).1
/-
**Submodule.FG.generators_ncard** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid 
M] [inst_2 : _root_.Module R M]   {p : Submodule R M}, p.FG → p.generators.ncard
 = p.spanFinrank
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submodule.fg_iff_spanRank_eq_spanFinrank`：fg_iff_spanRank_eq_spanFinrank
 {p : Submodule R M} : p.spanRank = p.spanFinrank ↔ p.FG
· 使用定理 `Set.ncard.eq_1`：∀ {α : Type u_1} (s : Set α), s.ncard = s.encard.toNat
· 使用定理 `Set.encard.eq_1`：∀ {α : Type u_1} (s : Set α), s.encard = ENat.card ↑s
· 使用定理 `ENat.card.eq_1`：∀ (α : Type u_3), ENat.card α = Cardinal.toENat (Cardina
l.mk α)
· 使用引理 `Submodule.generators_card`：generators_card (p : Submodule R M) : #(gener
ators p) = spanRank p
· 使用定理 `Cardinal.toNat_toENat`：∀ (a : Cardinal.{u_1}), (Cardinal.toENat a).toNat
 = Cardinal.toNat a
· 使用定理 `Submodule.spanFinrank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R
 M), p.spanFinra…
-/
lemma FG.generators_ncard {p : Submodule R M} (h : p.FG) :
    (generators p).ncard = spanFinrank p := by
  rw [← Nat.cast_inj (R := Cardinal), ← fg_iff_spanRank_eq_spanFinrank.mpr h, Set.ncard, Set.encard,
     ENat.card, generators_card, toNat_toENat, ← spanFinrank]
  exact (fg_iff_spanRank_eq_spanFinrank.mpr h).symm
/-
**Submodule.FG.finite_generators** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid 
M] [inst_2 : _root_.Module R M]   {p : Submodule R M}, p.FG → p.generators.Finit
e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lt_aleph0_iff_set_finite`：lt_aleph0_iff_set_finite {S : Set α} 
: #S < ℵ₀ ↔ S.Finite
· 使用引理 `Submodule.generators_card`：generators_card (p : Submodule R M) : #(gener
ators p) = spanRank p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submodule.spanRank_finite_iff_fg`：spanRank_finite_iff_fg {p : Submodule 
R M} : p.spanRank < aleph0 ↔ p.FG
-/
lemma FG.finite_generators {p : Submodule R M} (hp : p.FG) :
    p.generators.Finite := by
  rw [← Cardinal.lt_aleph0_iff_set_finite, Submodule.generators_card]
  exact spanRank_finite_iff_fg.mpr hp

/-- The span of the generators equals the submodule. -/
/-
**Submodule.span_generators** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：span_generators (p : Submodule R M) : span R (generators p) = p
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
The span of the generators equals the submodule.
-/
lemma span_generators (p : Submodule R M) : span R (generators p) = p :=
  (Classical.choose_spec (exists_span_set_card_eq_spanRank p)).2

/-- The elements of the generators are in the submodule. -/
/-
**Submodule.FG.generators_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid 
M] [inst_2 : _root_.Module R M]   (p : Submodule R M), p.generators ⊆ ↑p
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.span_generators`：span_generators (p : Submodule R M) : span R 
(generators p) = p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s

--- 原说明 ---
The elements of the generators are in the submodule.
-/
lemma FG.generators_mem (p : Submodule R M) : generators p ⊆ p := by
  nth_rw 2 [← span_generators p]
  exact subset_span (s := generators p)
/-
**Submodule.spanRank_sup_le_sum_spanRank** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_sup_le_sum_spanRank {p q : Submodule R M} : (p ⊔ q).spanRank <= p
.spanRank + q.spanRank
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.FG.spanRank_le_iff_exists_span_set_card_le`：∀ {R : Type u_1} {
M : Type u} [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modu
le R M]   (p : Submodule R M) {a : Cardina…
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `Cardinal.mk_union_le`：mk_union_le {α : Type u} (S T : Set α) : #(S union
 T : Set α) <= #S + #T
· 使用定理 `Submodule.span_union`：span_union (s t : Set M) : span R (s union t) = sp
an R s ⊔ span R t
-/
lemma spanRank_sup_le_sum_spanRank {p q : Submodule R M} :
    (p ⊔ q).spanRank ≤ p.spanRank + q.spanRank := by
  apply (FG.spanRank_le_iff_exists_span_set_card_le (p ⊔ q)).mpr
  obtain ⟨sp, ⟨hp₁, rfl⟩⟩ := exists_span_set_card_eq_spanRank p
  obtain ⟨sq, ⟨hq₁, rfl⟩⟩ := exists_span_set_card_eq_spanRank q
  exact ⟨sp ∪ sq, ⟨hp₁ ▸ hq₁ ▸ (Cardinal.mk_union_le sp sq), span_union sp sq⟩⟩
/-
**Submodule.spanFinrank_eq_zero_iff_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`
。
形式化陈述：spanFinrank_eq_zero_iff_eq_bot {p : Submodule R M} (h : p.FG) : p.spanFinr
ank = 0 ↔ p = ⊥
参数：h : p.FG。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.span_generators`：span_generators (p : Submodule R M) : span R 
(generators p) = p
· 使用定理 `Set.ncard_eq_zero`：∀ {α : Type u_1} {s : Set α}, autoParam s.Finite Set.
ncard_eq_zero._auto_1 → (s.ncard = 0 ↔ s = ∅)
· 使用定理 `Submodule.FG.finite_generators`：∀ {R : Type u_1} {M : Type u} [inst : Se
miring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p : Submodu
le R M}, p.FG → p.ge…
· 使用定理 `Submodule.FG.generators_ncard`：∀ {R : Type u_1} {M : Type u} [inst : Sem
iring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p : Submodul
e R M}, p.FG → p.ge…
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Submodule.spanFinrank_bot`：spanFinrank_bot : (⊥ : Submodule R M).spanFin
rank = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma spanFinrank_eq_zero_iff_eq_bot {p : Submodule R M} (h : p.FG) :
    p.spanFinrank = 0 ↔ p = ⊥ := by
  refine ⟨fun heq ↦ ?_, fun h ↦ by simp [h]⟩
  rw [← Submodule.FG.generators_ncard h, Set.ncard_eq_zero h.finite_generators] at heq
  rw [← p.span_generators, heq, span_empty]
/-
**Submodule.spanFinrank_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanFinrank_singleton {m : M} (hm : m != 0) : (span R {m}).spanFinrank = 1
参数：hm : m != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `Submodule.spanFinrank_span_le_ncard_of_finite`：spanFinrank_span_le_ncard
_of_finite {s : Set M} (hs : s.Finite) : (span R s).spanFinrank <= s.ncard
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ncard_singleton`：∀ {α : Type u_1} (a : α), {a}.ncard = 1
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Submodule.spanFinrank_eq_zero_iff_eq_bot`：spanFinrank_eq_zero_iff_eq_bot
 {p : Submodule R M} (h : p.FG) : p.spanFinrank = 0 ↔ p = ⊥
· 使用定理 `Submodule.fg_span_singleton`：fg_span_singleton (x : M) : FG (R ∙ x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
lemma spanFinrank_singleton {m : M} (hm : m ≠ 0) : (span R {m}).spanFinrank = 1 := by
  apply le_antisymm ?_ ?_
  · exact le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (by simp)) (by simp)
  · by_contra!
    simp [Submodule.spanFinrank_eq_zero_iff_eq_bot (fg_span_singleton m), hm] at this
/-
**Submodule.spanFinrank_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanFinrank_eq_one_iff (p : Submodule R M) : p.spanFinrank = 1 ↔ p.IsPrinc
ipal ∧ p != ⊥
参数：p : Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Submodule.spanRank_finite_iff_fg`：spanRank_finite_iff_fg {p : Submodule 
R M} : p.spanRank < aleph0 ↔ p.FG
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.FG.generators_ncard`：∀ {R : Type u_1} {M : Type u} [inst : Sem
iring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p : Submodul
e R M}, p.FG → p.ge…
· 使用引理 `Submodule.span_generators`：span_generators (p : Submodule R M) : span R 
(generators p) = p
· 使用引理 `Submodule.spanFinrank_singleton`：spanFinrank_singleton {m : M} (hm : m !
= 0) : (span R {m}).spanFinrank = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma spanFinrank_eq_one_iff (p : Submodule R M) : p.spanFinrank = 1 ↔ p.IsPrincipal ∧ p ≠ ⊥ := by
  refine ⟨fun h ↦ ⟨?_, (by grind [spanFinrank_bot])⟩,
    fun ⟨⟨a, ha⟩, _⟩ ↦ ha ▸ spanFinrank_singleton (by simp_all)⟩
  have fg : p.FG := spanRank_finite_iff_fg.1 (by simp_all [spanFinrank])
  obtain ⟨a, ha⟩ : ∃ a, p.generators = {a} := by simpa [← fg.generators_ncard] using h
  exact ⟨a, ha ▸ (p.span_generators).symm⟩

end Defs

end Submodule

section map

universe u v
namespace Submodule

section Semilinear

variable {R S : Type*} {M N : Type u} [Semiring R] [Semiring S] {σ : R →+* S}
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module S N]
  {L : Type v} [AddCommMonoid L] [Module S L]

/-
**Submodule.lift_spanRank_map_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：lift_spanRank_map_le [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) (p : Submodul
e R M) : Cardinal.lift.{u} (p.map f).spanRank <= Cardinal.lift.{v} p.spanRank
参数：f : M ->ₛₗ[σ] L；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.generators_card`：generators_card (p : Submodule R M) : #(gener
ators p) = spanRank p
· 使用引理 `Submodule.lift_spanRank_le_iff_exists_span_set_card_le`：lift_spanRank_le
_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal.{max u v}} : Card
inal.lift.{v} p.spanRank <= a ↔ exists s : S…
· 使用定理 `Cardinal.mk_image_le_lift`：mk_image_le_lift {α : Type u} {β : Type v} {f
 : α -> β} {s : Set α} : lift.{u} #(f '' s) <= lift.{v} #s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用引理 `Submodule.span_generators`：span_generators (p : Submodule R M) : span R 
(generators p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
-/
lemma lift_spanRank_map_le [RingHomSurjective σ] (f : M →ₛₗ[σ] L) (p : Submodule R M) :
    Cardinal.lift.{u} (p.map f).spanRank ≤ Cardinal.lift.{v} p.spanRank := by
  rw [← generators_card p, lift_spanRank_le_iff_exists_span_set_card_le]
  exact ⟨f '' p.generators, Cardinal.mk_image_le_lift, le_antisymm (span_le.2 (fun n ⟨m, hm, h⟩ ↦
    ⟨m, span_generators p ▸ subset_span hm, h⟩)) (by simp [span_generators])⟩
/-
**Submodule.spanRank_map_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_map_le [RingHomSurjective σ] (f : M ->ₛₗ[σ] N) (p : Submodule R M
) : (p.map f).spanRank <= p.spanRank
参数：f : M ->ₛₗ[σ] N；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用引理 `Submodule.lift_spanRank_map_le`：lift_spanRank_map_le [RingHomSurjective 
σ] (f : M ->ₛₗ[σ] L) (p : Submodule R M) : Cardinal.lift.{u} (p.map f).spanRank 
<= Cardinal.lift.{v}…
-/
lemma spanRank_map_le [RingHomSurjective σ] (f : M →ₛₗ[σ] N) (p : Submodule R M) :
    (p.map f).spanRank ≤ p.spanRank := by
  simpa using lift_spanRank_map_le f p
/-
**Submodule.spanFinrank_map_le_of_fg** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanFinrank_map_le_of_fg [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) {p : Subm
odule R M} (hp : p.FG) : (p.map f).spanFinrank <= p.spanFinrank
参数：f : M ->ₛₗ[σ] L；hp : p.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.FG.spanRank_le_iff`：∀ {R : Type u_1} {M : Type u} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p : Submodule
 R M}, p.FG → ∀ (n…
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Submodule.FG.spanRank_eq_spanFinrank`：∀ {R : Type u_1} {M : Type u} [ins
t : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p : S
ubmodule R M}, p.FG → p.sp…
· 使用引理 `Submodule.lift_spanRank_map_le`：lift_spanRank_map_le [RingHomSurjective 
σ] (f : M ->ₛₗ[σ] L) (p : Submodule R M) : Cardinal.lift.{u} (p.map f).spanRank 
<= Cardinal.lift.{v}…
-/
lemma spanFinrank_map_le_of_fg [RingHomSurjective σ] (f : M →ₛₗ[σ] L) {p : Submodule R M}
    (hp : p.FG) : (p.map f).spanFinrank ≤ p.spanFinrank := by
  rw [← (hp.map f).spanRank_le_iff, ← Cardinal.lift_le.{u}, Cardinal.lift_natCast,
    ← Cardinal.lift_natCast.{v}, ← hp.spanRank_eq_spanFinrank]
  exact p.lift_spanRank_map_le f
/-
**Submodule.lift_spanRank_map_eq_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Submodu
le`。
形式化陈述：lift_spanRank_map_eq_of_injective [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) 
(hf : Function.Injective f) (p : Submodule R M) : Cardinal.lift.{u} (p.map f).sp
anRank = Cardinal.lift.{v} p.spanRank
参数：f : M ->ₛₗ[σ] L；hf : Function.Injective f；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Submodule.lift_spanRank_map_le`：lift_spanRank_map_le [RingHomSurjective 
σ] (f : M ->ₛₗ[σ] L) (p : Submodule R M) : Cardinal.lift.{u} (p.map f).spanRank 
<= Cardinal.lift.{v}…
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.subset_range_iff_exists_image_eq`：subset_range_iff_exists_image_eq {
f : α -> β} {s : Set β} : s subseteq range f ↔ exists t, f '' t = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LinearMap.map_le_range`：map_le_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} {p : Submodule R M} : map f p <= range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_image_eq_lift`：mk_image_eq_lift {α : Type u} {β : Type v} (f
 : α -> β) (s : Set α) (h : Injective f) : lift.{u} #(f '' s) = lift.{v} #s
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Submodule.spanRank_span_le_card`：spanRank_span_le_card (s : Set M) : (Su
bmodule.span R s).spanRank <= #s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
-/
lemma lift_spanRank_map_eq_of_injective [RingHomSurjective σ] (f : M →ₛₗ[σ] L)
    (hf : Function.Injective f) (p : Submodule R M) :
    Cardinal.lift.{u} (p.map f).spanRank = Cardinal.lift.{v} p.spanRank := by
  refine (lift_spanRank_map_le f p).antisymm ?_
  obtain ⟨s, hs, e⟩ := (p.map f).exists_span_set_card_eq_spanRank
  obtain ⟨s, rfl⟩ : ∃ y, f '' y = s := Set.subset_range_iff_exists_image_eq.mp
    ((subset_span.trans e.le).trans LinearMap.map_le_range)
  obtain rfl : span R s = p := by simpa [(map_injective_of_injective hf).eq_iff] using e
  grw [← hs, Cardinal.mk_image_eq_lift _ _ hf, Cardinal.lift_le, spanRank_span_le_card]
/-
**Submodule.spanRank_map_eq_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_map_eq_of_injective [RingHomSurjective σ] (f : M ->ₛₗ[σ] N) (hf :
 Function.Injective f) (p : Submodule R M) : (p.map f).spanRank = p.spanRank
参数：f : M ->ₛₗ[σ] N；hf : Function.Injective f；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用引理 `Submodule.lift_spanRank_map_eq_of_injective`：lift_spanRank_map_eq_of_inj
ective [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) (hf : Function.Injective f) (p : 
Submodule R M) : Cardinal.lift.{u…
-/
lemma spanRank_map_eq_of_injective [RingHomSurjective σ] (f : M →ₛₗ[σ] N)
    (hf : Function.Injective f) (p : Submodule R M) : (p.map f).spanRank = p.spanRank := by
  simpa using lift_spanRank_map_eq_of_injective f hf p
/-
**Submodule.spanFinrank_map_eq_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Submodule
`。
形式化陈述：spanFinrank_map_eq_of_injective [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) (h
f : Function.Injective f) {p : Submodule R M} : (p.map f).spanFinrank = p.spanFi
nrank
参数：f : M ->ₛₗ[σ] L；hf : Function.Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.spanFinrank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R
 M), p.spanFinra…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用引理 `Submodule.lift_spanRank_map_eq_of_injective`：lift_spanRank_map_eq_of_inj
ective [RingHomSurjective σ] (f : M ->ₛₗ[σ] L) (hf : Function.Injective f) (p : 
Submodule R M) : Cardinal.lift.{u…
-/
lemma spanFinrank_map_eq_of_injective [RingHomSurjective σ] (f : M →ₛₗ[σ] L)
    (hf : Function.Injective f) {p : Submodule R M} :
    (p.map f).spanFinrank = p.spanFinrank := by
  rw [Submodule.spanFinrank, Submodule.spanFinrank, ← Cardinal.toNat_lift.{u, v},
    ← Cardinal.toNat_lift.{v, u}, lift_spanRank_map_eq_of_injective f hf p]
/-
**Submodule.spanRank_range_le** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_range_le [RingHomSurjective σ] (f : M ->ₛₗ[σ] N) : (LinearMap.ran
ge f).spanRank <= (⊤ : Submodule R M).spanRank
参数：f : M ->ₛₗ[σ] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用引理 `Submodule.spanRank_map_le`：spanRank_map_le [RingHomSurjective σ] (f : M 
->ₛₗ[σ] N) (p : Submodule R M) : (p.map f).spanRank <= p.spanRank
-/
lemma spanRank_range_le [RingHomSurjective σ] (f : M →ₛₗ[σ] N) :
    (LinearMap.range f).spanRank ≤ (⊤ : Submodule R M).spanRank := by
  simpa using spanRank_map_le f ⊤

@[simp]
/-
**Submodule.spanRank_top** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_top (p : Submodule R M) : (⊤ : Submodule R p).spanRank = p.spanRa
nk
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.spanRank_map_eq_of_injective`：spanRank_map_eq_of_injective [Ri
ngHomSurjective σ] (f : M ->ₛₗ[σ] N) (hf : Function.Injective f) (p : Submodule 
R M) : (p.map f).spanRank = …
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
-/
lemma spanRank_top (p : Submodule R M) : (⊤ : Submodule R p).spanRank = p.spanRank := by
  simpa using (spanRank_map_eq_of_injective _ p.subtype_injective ⊤).symm
/-
**Submodule.spanFinrank_top** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanFinrank_top (p : Submodule R M) : (⊤ : Submodule R p).spanFinrank = p.
spanFinrank
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.spanRank_top`：spanRank_top (p : Submodule R M) : (⊤ : Submodul
e R p).spanRank = p.spanRank
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma spanFinrank_top (p : Submodule R M) : (⊤ : Submodule R p).spanFinrank = p.spanFinrank := by
  simp [Submodule.spanFinrank]
/-
**Submodule.spanRank_eq_of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_eq_of_equiv {σ' : S ->+* R} [RingHomInvPair σ σ'] [RingHomInvPair
 σ' σ] (e : M ≃ₛₗ[σ] N) : (⊤ : Submodule R M).spanRank = (⊤ : Submodule S N).spa
nRank
参数：e : M ≃ₛₗ[σ] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.spanRank_map_eq_of_injective`：spanRank_map_eq_of_injective [Ri
ngHomSurjective σ] (f : M ->ₛₗ[σ] N) (hf : Function.Injective f) (p : Submodule 
R M) : (p.map f).spanRank = …
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
-/
lemma spanRank_eq_of_equiv
    {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : M ≃ₛₗ[σ] N) : (⊤ : Submodule R M).spanRank = (⊤ : Submodule S N).spanRank := by
  rw [← spanRank_map_eq_of_injective e.toLinearMap e.injective ⊤, map_top, LinearEquiv.range]

end Semilinear

section RestrictScalars

variable {R S : Type*} {M : Type u} [CommSemiring R] [Semiring S] [AddCommMonoid M]
  [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]

/-
**Submodule.le_spanRank_restrictScalars** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：le_spanRank_restrictScalars (N : Submodule S M) : N.spanRank <= (N.restric
tScalars R).spanRank
参数：N : Submodule S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Submodule.spanRank_span_le_card`：spanRank_span_le_card (s : Set M) : (Su
bmodule.span R s).spanRank <= #s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Submodule.span_le_restrictScalars`：span_le_restrictScalars : span R s <=
 (span S s).restrictScalars R
-/
lemma le_spanRank_restrictScalars (N : Submodule S M) :
    N.spanRank ≤ (N.restrictScalars R).spanRank := by
  obtain ⟨s, hs, e⟩ := (N.restrictScalars R).exists_span_set_card_eq_spanRank
  obtain rfl : span S s = N :=
    le_antisymm (span_le.mpr (span_le.mp e.le :)) (e.ge.trans (span_le_restrictScalars R S s))
  grw [← hs, spanRank_span_le_card]
/-
**Submodule.spanRank_restrictScalars_eq** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：spanRank_restrictScalars_eq (H : Function.Surjective (algebraMap R S)) (N 
: Submodule S M) : (N.restrictScalars R).spanRank = N.spanRank
参数：H : Function.Surjective (algebraMap R S)；N : Submodule S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用引理 `Submodule.le_spanRank_restrictScalars`：le_spanRank_restrictScalars (N : 
Submodule S M) : N.spanRank <= (N.restrictScalars R).spanRank
· 使用定理 `Submodule.exists_span_set_card_eq_spanRank`：exists_span_set_card_eq_span
Rank (p : Submodule R M) : exists s : Set M, #s = p.spanRank ∧ span R s = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.restrictScalars_span`：restrictScalars_span (hsur : Function.Su
rjective (algebraMap R A)) (X : Set M) : restrictScalars R (span A X) = span R X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用引理 `Submodule.spanRank_span_le_card`：spanRank_span_le_card (s : Set M) : (Su
bmodule.span R s).spanRank <= #s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma spanRank_restrictScalars_eq (H : Function.Surjective (algebraMap R S))
    (N : Submodule S M) : (N.restrictScalars R).spanRank = N.spanRank := by
  refine N.le_spanRank_restrictScalars.antisymm' ?_
  obtain ⟨s, hs, rfl⟩ := N.exists_span_set_card_eq_spanRank
  grw [restrictScalars_span R S H s, ← hs, spanRank_span_le_card]

end RestrictScalars

end Submodule

section Ideal

variable {R S : Type u} [Semiring R] [Semiring S] {T : Type v} [Semiring T]

open Submodule in
/-
**Ideal.lift_spanRank_map_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.lift_spanRank_map_le (f : R ->+* T) (I : Ideal R) : Cardinal.lift.{u
} (I.map f).spanRank <= Cardinal.lift.{v} I.spanRank
参数：f : R ->+* T；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.generators_card`：generators_card (p : Submodule R M) : #(gener
ators p) = spanRank p
· 使用引理 `Submodule.lift_spanRank_le_iff_exists_span_set_card_le`：lift_spanRank_le
_iff_exists_span_set_card_le (p : Submodule R M) {a : Cardinal.{max u v}} : Card
inal.lift.{v} p.spanRank <= a ↔ exists s : S…
· 使用定理 `Cardinal.mk_image_le_lift`：mk_image_le_lift {α : Type u} {β : Type v} {f
 : α -> β} {s : Set α} : lift.{u} #(f '' s) <= lift.{v} #s
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用引理 `Submodule.span_generators`：span_generators (p : Submodule R M) : span R 
(generators p) = p
· 使用定理 `Ideal.map_le_of_le_comap`：map_le_of_le_comap : I <= K.comap f -> I.map f
 <= K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.comap.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   (f f_1 : F),   f
 = f_1 → ∀ […
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
-/
lemma Ideal.lift_spanRank_map_le (f : R →+* T) (I : Ideal R) :
    Cardinal.lift.{u} (I.map f).spanRank ≤ Cardinal.lift.{v} I.spanRank := by
  rw [← generators_card I, lift_spanRank_le_iff_exists_span_set_card_le]
  refine ⟨f '' I.generators, Cardinal.mk_image_le_lift, le_antisymm (span_le.2 (fun s ⟨r, hr, hfr⟩ ↦
    hfr ▸ mem_map_of_mem _ <| span_generators I ▸ subset_span hr)) ?_⟩
  refine map_le_of_le_comap (fun r hr ↦ ?_)
  simp only [submodule_span_eq, mem_comap]
  rw [← map_span, ← submodule_span_eq, span_generators]
  exact mem_map_of_mem f hr
/-
**Ideal.lift_spanRank_map_eq_of_ringEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.lift_spanRank_map_eq_of_ringEquiv (f : R ≃+* T) (I : Ideal R) : Card
inal.lift.{u} (I.map f).spanRank = Cardinal.lift.{v} I.spanRank
参数：f : R ≃+* T；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用引理 `Ideal.lift_spanRank_map_le`：Ideal.lift_spanRank_map_le (f : R ->+* T) (I
 : Ideal R) : Cardinal.lift.{u} (I.map f).spanRank <= Cardinal.lift.{v} I.spanRa
nk
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_of_equiv`：map_of_equiv {I : Ideal R} (f : R ≃+* S) : (I.map (f
 : R ->+* S)).map (f.symm : S ->+* R) = I
-/
lemma Ideal.lift_spanRank_map_eq_of_ringEquiv (f : R ≃+* T) (I : Ideal R) :
    Cardinal.lift.{u} (I.map f).spanRank = Cardinal.lift.{v} I.spanRank := by
  apply (I.lift_spanRank_map_le (f : R →+* T)).antisymm
  nth_rw 1 [← Ideal.map_of_equiv f (I := I)]
  exact Ideal.lift_spanRank_map_le (f.symm : T →+* R) _
/-
**Ideal.spanRank_map_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.spanRank_map_le (f : R ->+* S) (I : Ideal R) : (I.map f).spanRank <=
 I.spanRank
参数：f : R ->+* S；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用引理 `Ideal.lift_spanRank_map_le`：Ideal.lift_spanRank_map_le (f : R ->+* T) (I
 : Ideal R) : Cardinal.lift.{u} (I.map f).spanRank <= Cardinal.lift.{v} I.spanRa
nk
-/
lemma Ideal.spanRank_map_le (f : R →+* S) (I : Ideal R) : (I.map f).spanRank ≤ I.spanRank := by
  simpa using I.lift_spanRank_map_le f

@[simp]
/-
**Ideal.spanRank_map_eq_of_ringEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.spanRank_map_eq_of_ringEquiv (f : R ≃+* S) (I : Ideal R) : (I.map f)
.spanRank = I.spanRank
参数：f : R ≃+* S；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用引理 `Ideal.lift_spanRank_map_eq_of_ringEquiv`：Ideal.lift_spanRank_map_eq_of_r
ingEquiv (f : R ≃+* T) (I : Ideal R) : Cardinal.lift.{u} (I.map f).spanRank = Ca
rdinal.lift.{v} I.spanRank
-/
lemma Ideal.spanRank_map_eq_of_ringEquiv (f : R ≃+* S) (I : Ideal R) :
    (I.map f).spanRank = I.spanRank := by
  simpa using I.lift_spanRank_map_eq_of_ringEquiv f
/-
**Ideal.spanFinrank_map_le_of_fg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.spanFinrank_map_le_of_fg (f : R ->+* T) {I : Ideal R} (hI : I.FG) : 
(I.map f).spanFinrank <= I.spanFinrank
参数：f : R ->+* T；hI : I.FG。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.FG.spanRank_le_iff`：∀ {R : Type u_1} {M : Type u} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p : Submodule
 R M}, p.FG → ∀ (n…
· 使用定理 `Ideal.FG.map`：∀ {R : Type u_3} {S : Type u_4} [inst : Semiring R] [inst_
1 : Semiring S] {I : Ideal R},   I.FG → ∀ (f : R →+* S), (Ideal.map f I).FG
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Submodule.FG.spanRank_eq_spanFinrank`：∀ {R : Type u_1} {M : Type u} [ins
t : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p : S
ubmodule R M}, p.FG → p.sp…
· 使用引理 `Ideal.lift_spanRank_map_le`：Ideal.lift_spanRank_map_le (f : R ->+* T) (I
 : Ideal R) : Cardinal.lift.{u} (I.map f).spanRank <= Cardinal.lift.{v} I.spanRa
nk
-/
lemma Ideal.spanFinrank_map_le_of_fg (f : R →+* T) {I : Ideal R} (hI : I.FG) :
    (I.map f).spanFinrank ≤ I.spanFinrank := by
  rw [← Submodule.FG.spanRank_le_iff (hI.map f), ← Cardinal.lift_le.{u}, Cardinal.lift_natCast,
    ← Cardinal.lift_natCast.{v}, ← Submodule.FG.spanRank_eq_spanFinrank hI]
  exact I.lift_spanRank_map_le f

@[simp]
/-
**Ideal.spanFinrank_map_eq_of_ringEquiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.spanFinrank_map_eq_of_ringEquiv (f : R ≃+* T) (I : Ideal R) : (I.map
 f).spanFinrank = I.spanFinrank
参数：f : R ≃+* T；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.spanFinrank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R
 M), p.spanFinra…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.toNat_lift`：toNat_lift (c : Cardinal.{v}) : toNat (lift.{u, v} 
c) = toNat c
· 使用引理 `Ideal.lift_spanRank_map_eq_of_ringEquiv`：Ideal.lift_spanRank_map_eq_of_r
ingEquiv (f : R ≃+* T) (I : Ideal R) : Cardinal.lift.{u} (I.map f).spanRank = Ca
rdinal.lift.{v} I.spanRank
-/
lemma Ideal.spanFinrank_map_eq_of_ringEquiv (f : R ≃+* T) (I : Ideal R) :
    (I.map f).spanFinrank = I.spanFinrank := by
  rw [Submodule.spanFinrank, Submodule.spanFinrank, ← Cardinal.toNat_lift.{u, v},
    ← Cardinal.toNat_lift.{v, u}, I.lift_spanRank_map_eq_of_ringEquiv f]

end Ideal

end map

section rank

open Cardinal Module Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-
**Module.Basis.mk_eq_spanRank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.Basis.mk_eq_spanRank [RankCondition R] {ι : Type*} (v : Basis ι R M
) : #(Set.range v) = (⊤ : Submodule R M).spanRank
参数：v : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用引理 `Submodule.spanRank_span_of_linearIndepOn`：spanRank_span_of_linearIndepOn
 [RankCondition R] (s : Set M) (hs : LinearIndepOn R id s) : (span R s).spanRank
 = #s
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
-/
lemma Module.Basis.mk_eq_spanRank [RankCondition R] {ι : Type*} (v : Basis ι R M) :
    #(Set.range v) = (⊤ : Submodule R M).spanRank := by
  rw [← v.span_eq, spanRank_span_of_linearIndepOn]
  exact v.linearIndependent.linearIndepOn_id
/-
**Submodule.rank_eq_spanRank_of_free** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.rank_eq_spanRank_of_free [Module.Free R M] [StrongRankCondition 
R] : Module.rank R M = (⊤ : Submodule R M).spanRank
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用引理 `Module.Basis.mk_eq_spanRank`：Module.Basis.mk_eq_spanRank [RankCondition 
R] {ι : Type*} (v : Basis ι R M) : #(Set.range v) = (⊤ : Submodule R M).spanRank
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `Module.Basis.injective`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [
inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b 
: Module.Bas…
-/
theorem Submodule.rank_eq_spanRank_of_free [Module.Free R M] [StrongRankCondition R] :
    Module.rank R M = (⊤ : Submodule R M).spanRank := by
  have := nontrivial_of_invariantBasisNumber R
  obtain ⟨I, B⟩ := ‹Module.Free R M›
  rw [← Basis.mk_eq_rank'' B, ← Basis.mk_eq_spanRank B, ← Cardinal.lift_id #(Set.range B),
    Cardinal.mk_range_eq_of_injective B.injective, Cardinal.lift_id _]
/-
**Module.finrank_eq_spanFinrank_of_free** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.finrank_eq_spanFinrank_of_free [StrongRankCondition R] [Module.Free
 R M] : Module.finrank R M = (⊤ : Submodule R M).spanFinrank
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.rank_eq_spanRank_of_free`：Submodule.rank_eq_spanRank_of_free [
Module.Free R M] [StrongRankCondition R] : Module.rank R M = (⊤ : Submodule R M)
.spanRank
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Module.finrank_eq_spanFinrank_of_free [StrongRankCondition R] [Module.Free R M] :
    Module.finrank R M = (⊤ : Submodule R M).spanFinrank := by
  simp [Module.finrank, Submodule.spanFinrank, Submodule.rank_eq_spanRank_of_free]
/-
**Submodule.rank_le_spanRank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.rank_le_spanRank [StrongRankCondition R] : Module.rank R M <= (⊤
 : Submodule R M).spanRank
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Submodule.spanRank.eq_1`：∀ {R : Type u_1} {M : Type u} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M)
, p.spanRank …
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
· 使用定理 `Submodule.instNonemptySubtypeSetEqSpan`：∀ {R : Type u_1} {M : Type u} [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p :
 Submodule R M), Nonempty { …
· 使用定理 `linearIndependent_le_span''`：linearIndependent_le_span'' {ι : Type v} {v
 : ι -> M} (i : LinearIndependent R v) (w : Set M) (s : span R w = ⊤) : #ι <= #w
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem Submodule.rank_le_spanRank [StrongRankCondition R] :
    Module.rank R M ≤ (⊤ : Submodule R M).spanRank := by
  rw [Module.rank, Submodule.spanRank]
  refine ciSup_le' (fun ι ↦ (le_ciInf fun s ↦ ?_))
  have := linearIndependent_le_span'' ι.2 s.1 s.2
  simpa

end rank

