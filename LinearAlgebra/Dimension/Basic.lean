/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Data.Set.Card

/-!
# Dimension of modules and vector spaces

## Main definitions

* The rank of a module is defined as `Module.rank : Cardinal`.
  This is defined as the supremum of the cardinalities of linearly independent subsets.

## Main statements

* `LinearMap.rank_le_of_injective`: the source of an injective linear map has dimension
  at most that of the target.
* `LinearMap.rank_le_of_surjective`: the target of a surjective linear map has dimension
  at most that of that source.

## Implementation notes

Many theorems in this file are not universe-generic when they relate dimensions
in different universes. They should be as general as they can be without
inserting `lift`s. The types `M`, `M'`, ... all live in different universes,
and `M₁`, `M₂`, ... all live in the same universe.
-/

@[expose] public section


noncomputable section

universe w w' u u' v v'

variable {R : Type u} {R' : Type u'} {M M₁ : Type v} {M' : Type v'}

open Cardinal Submodule Function Set

section Module

section

variable [Semiring R] [AddCommMonoid M] [Module R M]
variable (R M)

/-- The rank of a module, defined as a term of type `Cardinal`.

We define this as the supremum of the cardinalities of linearly independent subsets.
The supremum may not be attained, see https://mathoverflow.net/a/263053.

For a free module over any ring satisfying the strong rank condition
(e.g. left-Noetherian rings, commutative rings, and in particular division rings and fields),
this is the same as the dimension of the space (i.e. the cardinality of any basis).

In particular this agrees with the usual notion of the dimension of a vector space.

See also `Module.finrank` for a `ℕ`-valued function which returns the correct value
for a finite-dimensional vector space (but 0 for an infinite-dimensional vector space).
-/
@[stacks 09G3 "first part"]
protected irreducible_def Module.rank : Cardinal :=
  ⨆ ι : { s : Set M // LinearIndepOn R id s }, (#ι.1)

/-
**rank_le_card** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_le_card : Module.rank R M <= #M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
-/
theorem rank_le_card : Module.rank R M ≤ #M :=
  (Module.rank_def _ _).trans_le (ciSup_le' fun _ ↦ mk_set_le _)
/-
**nonempty_linearIndependent_set** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：nonempty_linearIndependent_set : Nonempty {s : Set M // LinearIndepOn R id
 s}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndepOn_empty`：linearIndepOn_empty : LinearIndepOn R v ∅
-/
instance nonempty_linearIndependent_set : Nonempty {s : Set M // LinearIndepOn R id s} :=
  ⟨⟨∅, linearIndepOn_empty _ _⟩⟩

end

namespace LinearIndependent
variable [Semiring R] [AddCommMonoid M] [Module R M]

variable [Nontrivial R]

/-
**LinearIndependent.cardinal_lift_le_rank** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndep
endent`。
形式化陈述：cardinal_lift_le_rank {ι : Type w} {v : ι -> M} (hv : LinearIndependent R 
v) : Cardinal.lift.{v} #ι <= Cardinal.lift.{w} (Module.rank R M)
参数：hv : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem cardinal_lift_le_rank {ι : Type w} {v : ι → M}
    (hv : LinearIndependent R v) :
    Cardinal.lift.{v} #ι ≤ Cardinal.lift.{w} (Module.rank R M) := by
  rw [Module.rank]
  refine le_trans ?_ (lift_le.mpr <| le_ciSup bddAbove_of_small ⟨_, hv.linearIndepOn_id⟩)
  exact lift_mk_le'.mpr ⟨(Equiv.ofInjective _ hv.injective).toEmbedding⟩
/-
**LinearIndependent.aleph0_le_rank** 是 Mathlib 中的一个引理，位于命名空间 `LinearIndependent`
。
形式化陈述：aleph0_le_rank {ι : Type w} [Infinite ι] {v : ι -> M} (hv : LinearIndepend
ent R v) : ℵ₀ <= Module.rank R M
参数：hv : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.aleph0_le_lift`：aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ <= lift.
{v} c ↔ ℵ₀ <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
-/
lemma aleph0_le_rank {ι : Type w} [Infinite ι] {v : ι → M}
    (hv : LinearIndependent R v) : ℵ₀ ≤ Module.rank R M :=
  aleph0_le_lift.mp <| (aleph0_le_lift.mpr <| aleph0_le_mk ι).trans hv.cardinal_lift_le_rank
/-
**LinearIndependent.cardinal_le_rank** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndependen
t`。
形式化陈述：cardinal_le_rank {ι : Type v} {v : ι -> M} (hv : LinearIndependent R v) : 
#ι <= Module.rank R M
参数：hv : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
-/
theorem cardinal_le_rank {ι : Type v} {v : ι → M}
    (hv : LinearIndependent R v) : #ι ≤ Module.rank R M := by
  simpa using hv.cardinal_lift_le_rank
/-
**LinearIndependent.cardinal_le_rank'** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndepende
nt`。
形式化陈述：cardinal_le_rank' {s : Set M} (hs : LinearIndependent R (fun x => x : s ->
 M)) : #s <= Module.rank R M
参数：hs : LinearIndependent R (fun x => x : s -> M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
-/
theorem cardinal_le_rank' {s : Set M}
    (hs : LinearIndependent R (fun x => x : s → M)) : #s ≤ Module.rank R M :=
  hs.cardinal_le_rank
/-
**LinearIndependent._root_.LinearIndepOn.encard_le_toENat_rank** 是 Mathlib 中的一个定
理，位于命名空间 `LinearIndependent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearIndepOn.encard_le_toENat_rank {ι : Type*} {v : ι → M} {s : Set ι}
    (hs : LinearIndepOn R v s) : s.encard ≤ (Module.rank R M).toENat := by
  simpa using OrderHom.mono (β := ℕ∞) Cardinal.toENat hs.linearIndependent.cardinal_lift_le_rank

end LinearIndependent

namespace Module

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-
**Module.exists_set_linearIndependent_of_lt_lift_rank** 是 Mathlib 中的一个定理，位于命名空间 
`Module`。
形式化陈述：exists_set_linearIndependent_of_lt_lift_rank {c : Cardinal.{w}} (h : Cardi
nal.lift.{v} c < Cardinal.lift.{w} (Module.rank R M)) : exists s : Set M, Cardin
al.lift.{w} #s = Cardinal.lift.{v} c ∧ LinearIndepOn R id s
参数：h : Cardinal.lift.{v} c < Cardinal.lift.{w} (Module.rank R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_lift_iff`：lt_lift_iff {a : Cardinal.{u}} {b : Cardinal.{max 
u v}} : b < lift.{v, u} a ↔ exists a' < a, lift.{v, u} a' = b
· 使用定理 `exists_lt_of_lt_ciSup`：exists_lt_of_lt_ciSup [Nonempty ι] {f : ι -> α} (
h : b < iSup f) : exists i, b < f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Cardinal.le_mk_iff_exists_subset`：le_mk_iff_exists_subset {c : Cardinal}
 {α : Type u} {s : Set α} : c <= #s ↔ exists p : Set α, p subseteq s ∧ #p = c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
-/
theorem exists_set_linearIndependent_of_lt_lift_rank {c : Cardinal.{w}}
    (h : Cardinal.lift.{v} c < Cardinal.lift.{w} (Module.rank R M)) :
    ∃ s : Set M, Cardinal.lift.{w} #s = Cardinal.lift.{v} c ∧ LinearIndepOn R id s := by
  rcases Cardinal.lt_lift_iff.mp h with ⟨c', hc', hcc'⟩
  rcases exists_lt_of_lt_ciSup (by simpa [← hcc', Module.rank_def] using h) with ⟨⟨s, hs⟩, h⟩
  rcases Cardinal.le_mk_iff_exists_subset.mp h.le with ⟨t, hst, ht⟩
  exact ⟨t, by simp [ht, hcc'], hs.mono hst⟩
/-
**Module.exists_set_linearIndependent_of_lt_rank** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le`。
形式化陈述：exists_set_linearIndependent_of_lt_rank {c : Cardinal.{v}} (h : c < Module
.rank R M) : exists s : Set M, #s = c ∧ LinearIndepOn R id s
参数：h : c < Module.rank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Module.exists_set_linearIndependent_of_lt_lift_rank`：exists_set_linearIn
dependent_of_lt_lift_rank {c : Cardinal.{w}} (h : Cardinal.lift.{v} c < Cardinal
.lift.{w} (Module.rank R M)) : exists s :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
-/
theorem exists_set_linearIndependent_of_lt_rank {c : Cardinal.{v}} (h : c < Module.rank R M) :
    ∃ s : Set M, #s = c ∧ LinearIndepOn R id s := by
  simpa using exists_set_linearIndependent_of_lt_lift_rank (Cardinal.lift_lt.mpr h)

variable [Nontrivial R]

-- TODO: the forward directions of the next few theorems don't need [Nontrivial R]
/-- Note: if the rank of a module is infinite, it may not contain a linear independent subset
with cardinality equal to the rank, see
https://mathoverflow.net/questions/263020/maximum-cardinal-of-a-set-of-linearly-independent-vectors-in-a-module. -/
/-
**Module.le_rank_iff_exists_finset** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：le_rank_iff_exists_finset {n : Nat} : n <= Module.rank R M ↔ exists s : Fi
nset M, s.card = n ∧ LinearIndepOn R id (s : Set M) where mp le
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Nat.cast_add_one`：cast_add_one (n : Nat) : ((n + 1 : Nat) : R) = n + 1
· 使用引理 `Cardinal.lt_natCast_add_one_iff`：lt_natCast_add_one_iff {n : Nat} {c : C
ardinal} : c < n + 1 ↔ c <= n
· 使用定理 `ciSup_le_iff`：ciSup_le_iff [Nonempty ι] {f : ι -> α} {a : α} (hf : BddAb
ove (range f)) : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.exists_finset_eq_card`：exists_finset_eq_card {α} {n : Nat} (h :
 n <= #α) : exists s : Finset α, n = s.card
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Cardinal.natCast_add_one_le_iff`：natCast_add_one_le_iff {n : Nat} {c : C
ardinal} : n + 1 <= c ↔ n < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Subtype.coe_preimage_self`：coe_preimage_self (s : Set α) : ((↑) : s -> α
) ⁻¹' s = univ
· 使用定理 `LE.le.trans_eq'`：∀ {α : Type u_1} {a b c : α} [inst : LE α], b ≤ a → b =
 c → c ≤ a
· 使用定理 `LinearIndependent.cardinal_le_rank'`：cardinal_le_rank' {s : Set M} (hs :
 LinearIndependent R (fun x => x : s -> M)) : #s <= Module.rank R M
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Note: if the rank of a module is infinite, it may not contain a linear independe
nt subset
with cardinality equal to the rank, see
https://mathoverflow.net/questions/263020/maximum-cardinal-of-a-set-of-linearly-
independent-vectors-in-a-module.
-/
theorem le_rank_iff_exists_finset {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ s : Finset M, s.card = n ∧ LinearIndepOn R id (s : Set M) where
  mp le := by
    contrapose! le
    obtain _ | n := n; · simp at le
    rw [Module.rank, Nat.cast_add_one, lt_natCast_add_one_iff, ciSup_le_iff bddAbove_of_small]
    intro s
    contrapose! le
    rw [← natCast_add_one_le_iff, ← Nat.cast_add_one] at le
    have ⟨t, ht⟩ := exists_finset_eq_card le
    exact ⟨t.map (.subtype _), by simpa using ht.symm, s.2.mono <| by simp⟩
  mpr := fun ⟨s, card_s, ind_s⟩ ↦ ind_s.cardinal_le_rank'.trans_eq' <| by simpa using card_s
/-
**Module.le_rank_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：le_rank_iff {n : Nat} : n <= Module.rank R M ↔ exists v : Fin n -> M, Line
arIndependent R v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Module.le_rank_iff_exists_finset`：le_rank_iff_exists_finset {n : Nat} : 
n <= Module.rank R M ↔ exists s : Finset M, s.card = n ∧ LinearIndepOn R id (s :
 Set M) where mp le
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndepOn_id_range_iff`：linearIndepOn_id_range_iff {ι} {f : ι -> M} 
(hf : Injective f) : LinearIndepOn R id (range f) ↔ LinearIndependent R f
-/
theorem le_rank_iff {n : ℕ} : n ≤ Module.rank R M ↔ ∃ v : Fin n → M, LinearIndependent R v := by
  refine le_rank_iff_exists_finset.trans ⟨fun ⟨s, s_card, s_ind⟩ ↦ ?_, fun ⟨v, v_ind⟩ ↦ ?_⟩
  · exact ⟨_, s_ind.comp _ (s.equivFinOfCardEq s_card).symm.injective⟩
  · refine ⟨.map ⟨_, v_ind.injective⟩ .univ, by simp, ?_⟩
    simpa using (linearIndepOn_id_range_iff v_ind.injective).mpr v_ind
/-
**Module.le_rank_iff_exists_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：le_rank_iff_exists_linearMap {n : Nat} : n <= Module.rank R M ↔ exists f :
 (Fin n -> R) ->ₗ[R] M, Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Module.le_rank_iff`：le_rank_iff {n : Nat} : n <= Module.rank R M ↔ exist
s v : Fin n -> M, LinearIndependent R v
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `LinearIndependent.map_injOn`：LinearIndependent.map_injOn (hv : LinearInd
ependent R v) (f : M ->ₗ[R] M') (hf_inj : Set.InjOn f (span R (Set.range v))) : 
LinearIndependent…
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
-/
theorem le_rank_iff_exists_linearMap {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ f : (Fin n → R) →ₗ[R] M, Injective f := by
  refine le_rank_iff.trans ⟨fun ⟨v, v_ind⟩ ↦ ?_, fun ⟨f, f_inj⟩ ↦
    ⟨_, (Module.Basis.ofEquivFun <| .refl ..).linearIndependent.map_injOn f f_inj.injOn⟩⟩
  have := Injective.comp v_ind (Finsupp.linearEquivFunOnFinite R ..).symm.injective
  exact ⟨Finsupp.linearCombination .. ∘ₗ _, this⟩

end Module

section SurjectiveInjective

section Semiring
variable [Semiring R] [AddCommMonoid M] [Module R M] [Semiring R']

variable (R M) in
@[nontriviality, simp]
/-
**rank_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_subsingleton [Subsingleton R] : Module.rank R M = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `ciSup_eq_of_forall_le_of_forall_lt_exists_gt`：ciSup_eq_of_forall_le_of_f
orall_lt_exists_gt [Nonempty ι] {f : ι -> α} (h₁ : forall i, f i <= b) (h₂ : for
all w, w < b -> exists i, w < f i)…
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `LinearIndepOn.of_subsingleton`：LinearIndepOn.of_subsingleton [Subsinglet
on R] : LinearIndepOn R v s
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_singleton`：mk_singleton {α : Type u} (x : α) : #({x} : Set α
) = 1
-/
theorem rank_subsingleton [Subsingleton R] : Module.rank R M = 1 := by
  rw [Module.rank_def, ciSup_eq_of_forall_le_of_forall_lt_exists_gt]
  · have := Module.subsingleton R M
    simp [Set.subsingleton_of_subsingleton]
  · intro w hw
    exact ⟨⟨{0}, LinearIndepOn.of_subsingleton⟩, hw.trans_eq (Cardinal.mk_singleton _).symm⟩
/-
**Module.one_le_rank_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.one_le_rank_iff : 1 <= Module.rank R M ↔ exists f : R ->ₗ[R] M, Inj
ective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Module.le_rank_iff_exists_linearMap`：le_rank_iff_exists_linearMap {n : N
at} : n <= Module.rank R M ↔ exists f : (Fin n -> R) ->ₗ[R] M, Injective f
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem Module.one_le_rank_iff : 1 ≤ Module.rank R M ↔ ∃ f : R →ₗ[R] M, Injective f := by
  nontriviality R
  refine le_rank_iff_exists_linearMap.trans ⟨fun ⟨f, hf⟩ ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
  · exact ⟨f ∘ₗ _, by apply hf.comp (LinearEquiv.piUnique R ..).symm.injective⟩
  · exact ⟨f ∘ₗ _, hf.comp (LinearEquiv.piUnique R ..).injective⟩
/-
**Module.rank_eq_zero_of_not_faithfulSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.rank_eq_zero_of_not_faithfulSMul (h : ¬ FaithfulSMul R M) : Module.
rank R M = 0
参数：h : ¬ FaithfulSMul R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.one_le_rank_iff`：Module.one_le_rank_iff : 1 <= Module.rank R M ↔ 
exists f : R ->ₗ[R] M, Injective f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem Module.rank_eq_zero_of_not_faithfulSMul (h : ¬ FaithfulSMul R M) : Module.rank R M = 0 := by
  contrapose! h
  obtain ⟨f, hf⟩ := by rwa [← Cardinal.one_le_iff_ne_zero, one_le_rank_iff] at h
  exact ⟨fun {x y} hxy ↦ hf (by simpa [← map_smul] using hxy (f 1))⟩

section
variable [AddCommMonoid M'] [Module R' M']

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is an injective map
non-zero elements, `j : M →+ M'` is an injective monoid homomorphism, such that the scalar
multiplications on `M` and `M'` are compatible, then the rank of `M / R` is smaller than or equal to
the rank of `M' / R'`. As a special case, taking `R = R'` it is
`LinearMap.lift_rank_le_of_injective`. -/
/-
**lift_rank_le_of_injective_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_le_of_injective_injective [AddCommGroup M'] [Module R' M'] (i : 
R' -> R) (j : M ->+ M') (hi : forall r, i r = 0 -> r = 0) (hj : Injective j) (hc
 : forall (r : R') (m : M), j (i r • m) = r • j m) : lift.{v'} (Module.rank R M)
 <= lift.{v} (Module.rank R' M')
参数：i : R' -> R；j : M ->+ M'；hi : forall r, i r = 0 -> r = 0；hj : Injective j；hc 
: forall (r : R') (m : M), j (i r • m) = r • j m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ciSup_mono_of_forall_exists'`：ciSup_mono_of_forall_exists' {ι'} {f : ι -
> α} {g : ι' -> α} (hg : BddAbove <| range g) (h : forall i, exists i', f i <= g
 i') : ⨆ i, f i <=…
· 使用定理 `LinearIndepOn.id_image`：LinearIndepOn.id_image (hs : LinearIndepOn R v s
) : LinearIndepOn R id (v '' s)
· 使用定理 `LinearIndependent.map_of_injective_injective`：LinearIndependent.map_of_i
njective_injective {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M'] (h
v : LinearIndependent R v) (i : R'…
· 使用定理 `LinearIndepOn.linearIndependent`：LinearIndepOn.linearIndependent {s : Se
t ι} (h : LinearIndepOn R v s) : LinearIndependent R (fun x : s => v x)
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)

--- 原说明 ---
If `M / R` and `M' / R'` are modules, `i : R' → R` is an injective map
non-zero elements, `j : M →+ M'` is an injective monoid homomorphism, such that 
the scalar
multiplications on `M` and `M'` are compatible, then the rank of `M / R` is smal
ler than or equal to
the rank of `M' / R'`. As a special case, taking `R = R'` it is
`LinearMap.lift_rank_le_of_injective`.
-/
theorem lift_rank_le_of_injective_injectiveₛ (i : R' → R) (j : M →+ M')
    (hi : Injective i) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    lift.{v'} (Module.rank R M) ≤ lift.{v} (Module.rank R' M') := by
  simp_rw [Module.rank, lift_iSup bddAbove_of_small]
  exact ciSup_mono_of_forall_exists' bddAbove_of_small fun ⟨s, h⟩ ↦ ⟨⟨j '' s,
    LinearIndepOn.id_image (h.linearIndependent.map_of_injective_injectiveₛ i j hi hj hc)⟩,
    lift_mk_le'.mpr ⟨(Equiv.Set.image j s hj).toEmbedding⟩⟩

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map, and
`j : M →+ M'` is an injective monoid homomorphism, such that the scalar multiplications on `M` and
`M'` are compatible, then the rank of `M / R` is smaller than or equal to the rank of `M' / R'`.
As a special case, taking `R = R'` it is `LinearMap.lift_rank_le_of_injective`. -/
/-
**lift_rank_le_of_surjective_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_le_of_surjective_injective (i : R -> R') (j : M ->+ M') (hi : Su
rjective i) (hj : Injective j) (hc : forall (r : R) (m : M), j (r • m) = i r • j
 m) : lift.{v'} (Module.rank R M) <= lift.{v} (Module.rank R' M')
参数：i : R -> R'；j : M ->+ M'；hi : Surjective i；hj : Injective j；hc : forall (r : 
R) (m : M), j (r • m) = i r • j m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Surjective.hasRightInverse`：∀ {α : Sort u} {β : Sort v} {f : α 
→ β}, Function.Surjective f → Function.HasRightInverse f
· 使用定理 `lift_rank_le_of_injective_injectiveₛ`：lift_rank_le_of_injective_injectiv
eₛ (i : R' -> R) (j : M ->+ M') (hi : Injective i) (hj : Injective j) (hc : fora
ll (r : R') (m : M), j (i …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `M / R` and `M' / R'` are modules, `i : R → R'` is a surjective map, and
`j : M →+ M'` is an injective monoid homomorphism, such that the scalar multipli
cations on `M` and
`M'` are compatible, then the rank of `M / R` is smaller than or equal to the ra
nk of `M' / R'`.
As a special case, taking `R = R'` it is `LinearMap.lift_rank_le_of_injective`.
-/
theorem lift_rank_le_of_surjective_injective (i : R → R') (j : M →+ M')
    (hi : Surjective i) (hj : Injective j) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    lift.{v'} (Module.rank R M) ≤ lift.{v} (Module.rank R' M') := by
  obtain ⟨i', hi'⟩ := hi.hasRightInverse
  refine lift_rank_le_of_injective_injectiveₛ i' j (fun _ _ h ↦ ?_) hj fun r m ↦ ?_
  · apply_fun i at h
    rwa [hi', hi'] at h
  rw [hc (i' r) m, hi']

/-- If `M / R` and `M' / R'` are modules, `i : R → R'` is a bijective map which maps zero to zero,
`j : M ≃+ M'` is a group isomorphism, such that the scalar multiplications on `M` and `M'` are
compatible, then the rank of `M / R` is equal to the rank of `M' / R'`.
As a special case, taking `R = R'` it is `LinearEquiv.lift_rank_eq`. -/
/-
**lift_rank_eq_of_equiv_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_eq_of_equiv_equiv (i : R -> R') (j : M ≃+ M') (hi : Bijective i)
 (hc : forall (r : R) (m : M), j (r • m) = i r • j m) : lift.{v'} (Module.rank R
 M) = lift.{v} (Module.rank R' M')
参数：i : R -> R'；j : M ≃+ M'；hi : Bijective i；hc : forall (r : R) (m : M), j (r • 
m) = i r • j m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `lift_rank_le_of_surjective_injective`：lift_rank_le_of_surjective_injecti
ve (i : R -> R') (j : M ->+ M') (hi : Surjective i) (hj : Injective j) (hc : for
all (r : R) (m : M), j (r …
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `lift_rank_le_of_injective_injectiveₛ`：lift_rank_le_of_injective_injectiv
eₛ (i : R' -> R) (j : M ->+ M') (hi : Injective i) (hj : Injective j) (hc : fora
ll (r : R') (m : M), j (i …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AddEquiv.symm_apply_eq`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [
inst_1 : Add N] (e : M ≃+ N) {x : N} {y : M}, e.symm x = y ↔ x = e y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `M / R` and `M' / R'` are modules, `i : R → R'` is a bijective map which maps
 zero to zero,
`j : M ≃+ M'` is a group isomorphism, such that the scalar multiplications on `M
` and `M'` are
compatible, then the rank of `M / R` is equal to the rank of `M' / R'`.
As a special case, taking `R = R'` it is `LinearEquiv.lift_rank_eq`.
-/
theorem lift_rank_eq_of_equiv_equiv (i : R → R') (j : M ≃+ M')
    (hi : Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    lift.{v'} (Module.rank R M) = lift.{v} (Module.rank R' M') :=
  (lift_rank_le_of_surjective_injective i j hi.2 j.injective hc).antisymm <|
    lift_rank_le_of_injective_injectiveₛ i j.symm hi.1
      j.symm.injective fun _ _ ↦ j.symm_apply_eq.2 <| by simp_all
end

section
variable [AddCommMonoid M₁] [Module R' M₁]

/-- The same-universe version of `lift_rank_le_of_injective_injective`. -/
/-
**rank_le_of_injective_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_le_of_injective_injective [AddCommGroup M₁] [Module R' M₁] (i : R' ->
 R) (j : M ->+ M₁) (hi : forall r, i r = 0 -> r = 0) (hj : Injective j) (hc : fo
rall (r : R') (m : M), j (i r • m) = r • j m) : Module.rank R M <= Module.rank R
' M₁
参数：i : R' -> R；j : M ->+ M₁；hi : forall r, i r = 0 -> r = 0；hj : Injective j；hc 
: forall (r : R') (m : M), j (i r • m) = r • j m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_rank_le_of_injective_injective`：lift_rank_le_of_injective_injective
 [AddCommGroup M'] [Module R' M'] (i : R' -> R) (j : M ->+ M') (hi : forall r, i
 r = 0 -> r = 0) (hj : In…

--- 原说明 ---
The same-universe version of `lift_rank_le_of_injective_injective`.
-/
theorem rank_le_of_injective_injectiveₛ (i : R' → R) (j : M →+ M₁)
    (hi : Injective i) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    Module.rank R M ≤ Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_injective_injectiveₛ i j hi hj hc

/-- The same-universe version of `lift_rank_le_of_surjective_injective`. -/
/-
**rank_le_of_surjective_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_le_of_surjective_injective (i : R -> R') (j : M ->+ M₁) (hi : Surject
ive i) (hj : Injective j) (hc : forall (r : R) (m : M), j (r • m) = i r • j m) :
 Module.rank R M <= Module.rank R' M₁
参数：i : R -> R'；j : M ->+ M₁；hi : Surjective i；hj : Injective j；hc : forall (r : 
R) (m : M), j (r • m) = i r • j m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_rank_le_of_surjective_injective`：lift_rank_le_of_surjective_injecti
ve (i : R -> R') (j : M ->+ M') (hi : Surjective i) (hj : Injective j) (hc : for
all (r : R) (m : M), j (r …

--- 原说明 ---
The same-universe version of `lift_rank_le_of_surjective_injective`.
-/
theorem rank_le_of_surjective_injective (i : R → R') (j : M →+ M₁)
    (hi : Surjective i) (hj : Injective j)
    (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.rank R M ≤ Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

/-- The same-universe version of `lift_rank_eq_of_equiv_equiv`. -/
/-
**rank_eq_of_equiv_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_eq_of_equiv_equiv (i : R -> R') (j : M ≃+ M₁) (hi : Bijective i) (hc 
: forall (r : R) (m : M), j (r • m) = i r • j m) : Module.rank R M = Module.rank
 R' M₁
参数：i : R -> R'；j : M ≃+ M₁；hi : Bijective i；hc : forall (r : R) (m : M), j (r • 
m) = i r • j m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_rank_eq_of_equiv_equiv`：lift_rank_eq_of_equiv_equiv (i : R -> R') (
j : M ≃+ M') (hi : Bijective i) (hc : forall (r : R) (m : M), j (r • m) = i r • 
j m) : lift.{v'} …

--- 原说明 ---
The same-universe version of `lift_rank_eq_of_equiv_equiv`.
-/
theorem rank_eq_of_equiv_equiv (i : R → R') (j : M ≃+ M₁)
    (hi : Bijective i) (hc : ∀ (r : R) (m : M), j (r • m) = i r • j m) :
    Module.rank R M = Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hi hc

end
end Semiring

set_option backward.isDefEq.respectTransparency false in
/-- TODO: prove that nontrivial commutative semirings satisfy the strong rank condition,
following *Free sets and free subsemimodules in a semimodule* by Yi-Jia Tan, Theorem 3.2.

Rings `R` that fail the strong rank condition but satisfy `rank R R = 1` are expected to exist, see
https://mathoverflow.net/questions/317422/rings-that-fail-to-satisfy-the-strong-rank-condition. -/
/-
**CommSemiring.rank_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CommSemiring.rank_self (R) [CommSemiring R] : Module.rank R R = 1
参数：R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Cardinal.two_le_iff_one_lt`：two_le_iff_one_lt {c : Cardinal} : 2 <= c ↔ 
1 < c
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)
· 使用定理 `Module.le_rank_iff_exists_linearMap`：le_rank_iff_exists_linearMap {n : N
at} : n <= Module.rank R M ↔ exists f : (Fin n -> R) ->ₗ[R] M, Injective f
· 使用定理 `Module.one_le_rank_iff`：Module.one_le_rank_iff : 1 <= Module.rank R M ↔ 
exists f : R ->ₗ[R] M, Injective f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
TODO: prove that nontrivial commutative semirings satisfy the strong rank condit
ion,
following *Free sets and free subsemimodules in a semimodule* by Yi-Jia Tan, The
orem 3.2.

Rings `R` that fail the strong rank condition but satisfy `rank R R = 1` are exp
ected to exist, see
https://mathoverflow.net/questions/317422/rings-that-fail-to-satisfy-the-strong-
rank-condition.
-/
theorem CommSemiring.rank_self (R) [CommSemiring R] : Module.rank R R = 1 := by
  nontriviality R
  rw [le_antisymm_iff, ← not_lt, ← two_le_iff_one_lt, ← Nat.cast_two,
    Module.le_rank_iff_exists_linearMap, Module.one_le_rank_iff]
  refine ⟨fun ⟨f, inj⟩ ↦ ?_, _, (LinearEquiv.refl ..).injective⟩
  have := inj (a₁ := f ![0, 1] • ![1, 0]) (a₂ := f ![1, 0] • ![0, 1]) <| by
    simp_rw [map_smul, smul_eq_mul]; apply mul_comm
  have h₁ : f ![0, 1] = 0 := by simpa using congr($this 0)
  have h₂ : 0 = f ![1, 0] := by simpa using congr($this 1)
  exact zero_ne_one (α := R) (by simpa using congr($(inj (h₁.trans h₂)) 1))

section Ring
variable [Ring R] [AddCommGroup M] [Module R M] [Ring R']

/-- If `M / R` and `M' / R'` are modules, `i : R' → R` is a map which sends non-zero elements to
non-zero elements, `j : M →+ M'` is an injective group homomorphism, such that the scalar
multiplications on `M` and `M'` are compatible, then the rank of `M / R` is smaller than or equal to
the rank of `M' / R'`. As a special case, taking `R = R'` it is
`LinearMap.lift_rank_le_of_injective`. -/
/-
**lift_rank_le_of_injective_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_le_of_injective_injective [AddCommGroup M'] [Module R' M'] (i : 
R' -> R) (j : M ->+ M') (hi : forall r, i r = 0 -> r = 0) (hj : Injective j) (hc
 : forall (r : R') (m : M), j (i r • m) = r • j m) : lift.{v'} (Module.rank R M)
 <= lift.{v} (Module.rank R' M')
参数：i : R' -> R；j : M ->+ M'；hi : forall r, i r = 0 -> r = 0；hj : Injective j；hc 
: forall (r : R') (m : M), j (i r • m) = r • j m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ciSup_mono_of_forall_exists'`：ciSup_mono_of_forall_exists' {ι'} {f : ι -
> α} {g : ι' -> α} (hg : BddAbove <| range g) (h : forall i, exists i', f i <= g
 i') : ⨆ i, f i <=…
· 使用定理 `LinearIndepOn.id_image`：LinearIndepOn.id_image (hs : LinearIndepOn R v s
) : LinearIndepOn R id (v '' s)
· 使用定理 `LinearIndependent.map_of_injective_injective`：LinearIndependent.map_of_i
njective_injective {R' M' : Type*} [Ring R'] [AddCommGroup M'] [Module R' M'] (h
v : LinearIndependent R v) (i : R'…
· 使用定理 `LinearIndepOn.linearIndependent`：LinearIndepOn.linearIndependent {s : Se
t ι} (h : LinearIndepOn R v s) : LinearIndependent R (fun x : s => v x)
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)

--- 原说明 ---
If `M / R` and `M' / R'` are modules, `i : R' → R` is a map which sends non-zero
 elements to
non-zero elements, `j : M →+ M'` is an injective group homomorphism, such that t
he scalar
multiplications on `M` and `M'` are compatible, then the rank of `M / R` is smal
ler than or equal to
the rank of `M' / R'`. As a special case, taking `R = R'` it is
`LinearMap.lift_rank_le_of_injective`.
-/
theorem lift_rank_le_of_injective_injective [AddCommGroup M'] [Module R' M']
    (i : R' → R) (j : M →+ M') (hi : ∀ r, i r = 0 → r = 0) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    lift.{v'} (Module.rank R M) ≤ lift.{v} (Module.rank R' M') := by
  simp_rw [Module.rank, lift_iSup bddAbove_of_small]
  exact ciSup_mono_of_forall_exists' bddAbove_of_small fun ⟨s, h⟩ ↦
    ⟨⟨j '' s, LinearIndepOn.id_image <| h.linearIndependent.map_of_injective_injective i j hi
      (fun _ _ ↦ hj <| by rwa [j.map_zero]) hc⟩,
    lift_mk_le'.mpr ⟨(Equiv.Set.image j s hj).toEmbedding⟩⟩

/-- The same-universe version of `lift_rank_le_of_injective_injective`. -/
/-
**rank_le_of_injective_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_le_of_injective_injective [AddCommGroup M₁] [Module R' M₁] (i : R' ->
 R) (j : M ->+ M₁) (hi : forall r, i r = 0 -> r = 0) (hj : Injective j) (hc : fo
rall (r : R') (m : M), j (i r • m) = r • j m) : Module.rank R M <= Module.rank R
' M₁
参数：i : R' -> R；j : M ->+ M₁；hi : forall r, i r = 0 -> r = 0；hj : Injective j；hc 
: forall (r : R') (m : M), j (i r • m) = r • j m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_rank_le_of_injective_injective`：lift_rank_le_of_injective_injective
 [AddCommGroup M'] [Module R' M'] (i : R' -> R) (j : M ->+ M') (hi : forall r, i
 r = 0 -> r = 0) (hj : In…

--- 原说明 ---
The same-universe version of `lift_rank_le_of_injective_injective`.
-/
theorem rank_le_of_injective_injective [AddCommGroup M₁] [Module R' M₁]
    (i : R' → R) (j : M →+ M₁) (hi : ∀ r, i r = 0 → r = 0) (hj : Injective j)
    (hc : ∀ (r : R') (m : M), j (i r • m) = r • j m) :
    Module.rank R M ≤ Module.rank R' M₁ := by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

end Ring

namespace Algebra

variable {R : Type w} {S : Type v} [CommSemiring R] [Semiring S] [Algebra R S]
  {R' : Type w'} {S' : Type v'} [CommSemiring R'] [Semiring S'] [Algebra R' S']

/-- If `S / R` and `S' / R'` are algebras, `i : R' →+* R` and `j : S →+* S'` are injective ring
homomorphisms, such that `R' → R → S → S'` and `R' → S'` commute, then the rank of `S / R` is
smaller than or equal to the rank of `S' / R'`. -/
/-
**Algebra.lift_rank_le_of_injective_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
`。
形式化陈述：lift_rank_le_of_injective_injective (i : R' ->+* R) (j : S ->+* S') (hi : 
Injective i) (hj : Injective j) (hc : (j.comp (algebraMap R S)).comp i = algebra
Map R' S') : lift.{v'} (Module.rank R S) <= lift.{v} (Module.rank R' S')
参数：i : R' ->+* R；j : S ->+* S'；hi : Injective i；hj : Injective j；hc : (j.comp (a
lgebraMap R S)).comp i = algebraMap R' S'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lift_rank_le_of_injective_injectiveₛ`：lift_rank_le_of_injective_injectiv
eₛ (i : R' -> R) (j : M ->+ M') (hi : Injective i) (hj : Injective j) (hc : fora
ll (r : R') (m : M), j (i …
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `S / R` and `S' / R'` are algebras, `i : R' →+* R` and `j : S →+* S'` are inj
ective ring
homomorphisms, such that `R' → R → S → S'` and `R' → S'` commute, then the rank 
of `S / R` is
smaller than or equal to the rank of `S' / R'`.
-/
theorem lift_rank_le_of_injective_injective
    (i : R' →+* R) (j : S →+* S') (hi : Injective i) (hj : Injective j)
    (hc : (j.comp (algebraMap R S)).comp i = algebraMap R' S') :
    lift.{v'} (Module.rank R S) ≤ lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_le_of_injective_injectiveₛ i j hi hj fun r _ ↦ ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp_rw [smul_def, AddMonoidHom.coe_coe, map_mul, this]

/-- If `S / R` and `S' / R'` are algebras, `i : R →+* R'` is a surjective ring homomorphism,
`j : S →+* S'` is an injective ring homomorphism, such that `R → R' → S'` and `R → S → S'` commute,
then the rank of `S / R` is smaller than or equal to the rank of `S' / R'`. -/
/-
**Algebra.lift_rank_le_of_surjective_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a`。
形式化陈述：lift_rank_le_of_surjective_injective (i : R ->+* R') (j : S ->+* S') (hi :
 Surjective i) (hj : Injective j) (hc : (algebraMap R' S').comp i = j.comp (alge
braMap R S)) : lift.{v'} (Module.rank R S) <= lift.{v} (Module.rank R' S')
参数：i : R ->+* R'；j : S ->+* S'；hi : Surjective i；hj : Injective j；hc : (algebraM
ap R' S').comp i = j.comp (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lift_rank_le_of_surjective_injective`：lift_rank_le_of_surjective_injecti
ve (i : R -> R') (j : M ->+ M') (hi : Surjective i) (hj : Injective j) (hc : for
all (r : R) (m : M), j (r …
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `S / R` and `S' / R'` are algebras, `i : R →+* R'` is a surjective ring homom
orphism,
`j : S →+* S'` is an injective ring homomorphism, such that `R → R' → S'` and `R
 → S → S'` commute,
then the rank of `S / R` is smaller than or equal to the rank of `S' / R'`.
-/
theorem lift_rank_le_of_surjective_injective
    (i : R →+* R') (j : S →+* S') (hi : Surjective i) (hj : Injective j)
    (hc : (algebraMap R' S').comp i = j.comp (algebraMap R S)) :
    lift.{v'} (Module.rank R S) ≤ lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_le_of_surjective_injective i j hi hj fun r _ ↦ ?_
  have := congr($hc r)
  simp only [RingHom.coe_comp, comp_apply] at this
  simp only [smul_def, AddMonoidHom.coe_coe, map_mul, this]

/-- If `S / R` and `S' / R'` are algebras, `i : R ≃+* R'` and `j : S ≃+* S'` are
ring isomorphisms, such that `R → R' → S'` and `R → S → S'` commute,
then the rank of `S / R` is equal to the rank of `S' / R'`. -/
/-
**Algebra.lift_rank_eq_of_equiv_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：lift_rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S') (hc : (algebraMa
p R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) : lift.{v'} (Modu
le.rank R S) = lift.{v} (Module.rank R' S')
参数：i : R ≃+* R'；j : S ≃+* S'；hc : (algebraMap R' S').comp i.toRingHom = j.toRing
Hom.comp (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lift_rank_eq_of_equiv_equiv`：lift_rank_eq_of_equiv_equiv (i : R -> R') (
j : M ≃+ M') (hi : Bijective i) (hc : forall (r : R) (m : M), j (r • m) = i r • 
j m) : lift.{v'} …
· 使用定理 `RingEquivClass.toAddEquivClass`：∀ {F : Type u_1} {R : Type u_4} {S : Typ
e u_5} [inst : EquivLike F R S] [inst_1 : Mul R] [inst_2 : Add R]   [inst_3 : Mu
l S] [inst_4 : Add S…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingEquiv.bijective`：∀ {R : Type u_4} {S : Type u_5} [inst : Mul R] [ins
t_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S] (e : R ≃+* S),   Function.Bijecti
ve ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `S / R` and `S' / R'` are algebras, `i : R ≃+* R'` and `j : S ≃+* S'` are
ring isomorphisms, such that `R → R' → S'` and `R → S → S'` commute,
then the rank of `S / R` is equal to the rank of `S' / R'`.
-/
theorem lift_rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S')
    (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) :
    lift.{v'} (Module.rank R S) = lift.{v} (Module.rank R' S') := by
  refine _root_.lift_rank_eq_of_equiv_equiv i j i.bijective fun r _ ↦ ?_
  have := congr($hc r)
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, comp_apply] at this
  simp only [smul_def, RingEquiv.coe_toAddEquiv, map_mul, this]

variable {S' : Type v} [Semiring S'] [Algebra R' S']

/-- The same-universe version of `Algebra.lift_rank_le_of_injective_injective`. -/
/-
**Algebra.rank_le_of_injective_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：rank_le_of_injective_injective (i : R' ->+* R) (j : S ->+* S') (hi : Injec
tive i) (hj : Injective j) (hc : (j.comp (algebraMap R S)).comp i = algebraMap R
' S') : Module.rank R S <= Module.rank R' S'
参数：i : R' ->+* R；j : S ->+* S'；hi : Injective i；hj : Injective j；hc : (j.comp (a
lgebraMap R S)).comp i = algebraMap R' S'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Algebra.lift_rank_le_of_injective_injective`：lift_rank_le_of_injective_i
njective (i : R' ->+* R) (j : S ->+* S') (hi : Injective i) (hj : Injective j) (
hc : (j.comp (algebraMap R S)).co…

--- 原说明 ---
The same-universe version of `Algebra.lift_rank_le_of_injective_injective`.
-/
theorem rank_le_of_injective_injective
    (i : R' →+* R) (j : S →+* S') (hi : Injective i) (hj : Injective j)
    (hc : (j.comp (algebraMap R S)).comp i = algebraMap R' S') :
    Module.rank R S ≤ Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_le_of_injective_injective i j hi hj hc

/-- The same-universe version of `Algebra.lift_rank_le_of_surjective_injective`. -/
/-
**Algebra.rank_le_of_surjective_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：rank_le_of_surjective_injective (i : R ->+* R') (j : S ->+* S') (hi : Surj
ective i) (hj : Injective j) (hc : (algebraMap R' S').comp i = j.comp (algebraMa
p R S)) : Module.rank R S <= Module.rank R' S'
参数：i : R ->+* R'；j : S ->+* S'；hi : Surjective i；hj : Injective j；hc : (algebraM
ap R' S').comp i = j.comp (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Algebra.lift_rank_le_of_surjective_injective`：lift_rank_le_of_surjective
_injective (i : R ->+* R') (j : S ->+* S') (hi : Surjective i) (hj : Injective j
) (hc : (algebraMap R' S').comp i …

--- 原说明 ---
The same-universe version of `Algebra.lift_rank_le_of_surjective_injective`.
-/
theorem rank_le_of_surjective_injective
    (i : R →+* R') (j : S →+* S') (hi : Surjective i) (hj : Injective j)
    (hc : (algebraMap R' S').comp i = j.comp (algebraMap R S)) :
    Module.rank R S ≤ Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_le_of_surjective_injective i j hi hj hc

/-- The same-universe version of `Algebra.lift_rank_eq_of_equiv_equiv`. -/
/-
**Algebra.rank_eq_of_equiv_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
形式化陈述：rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S') (hc : (algebraMap R' 
S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) : Module.rank R S = Mo
dule.rank R' S'
参数：i : R ≃+* R'；j : S ≃+* S'；hc : (algebraMap R' S').comp i.toRingHom = j.toRing
Hom.comp (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Algebra.lift_rank_eq_of_equiv_equiv`：lift_rank_eq_of_equiv_equiv (i : R 
≃+* R') (j : S ≃+* S') (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.c
omp (algebraMap R S)) : l…

--- 原说明 ---
The same-universe version of `Algebra.lift_rank_eq_of_equiv_equiv`.
-/
theorem rank_eq_of_equiv_equiv (i : R ≃+* R') (j : S ≃+* S')
    (hc : (algebraMap R' S').comp i.toRingHom = j.toRingHom.comp (algebraMap R S)) :
    Module.rank R S = Module.rank R' S' := by
  simpa only [lift_id] using lift_rank_eq_of_equiv_equiv i j hc

end Algebra

end SurjectiveInjective

variable [Semiring R] [AddCommMonoid M] [Module R M]
  [Semiring R'] [AddCommMonoid M'] [AddCommMonoid M₁]
  [Module R M'] [Module R M₁] [Module R' M'] [Module R' M₁]

section

/-
**LinearMap.lift_rank_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.lift_rank_le_of_injective (f : M ->ₗ[R] M') (i : Injective f) : 
Cardinal.lift.{v'} (Module.rank R M) <= Cardinal.lift.{v} (Module.rank R M')
参数：f : M ->ₗ[R] M'；i : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lift_rank_le_of_injective_injectiveₛ`：lift_rank_le_of_injective_injectiv
eₛ (i : R' -> R) (j : M ->+ M') (hi : Injective i) (hj : Injective j) (hc : fora
ll (r : R') (m : M), j (i …
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
theorem LinearMap.lift_rank_le_of_injective (f : M →ₗ[R] M') (i : Injective f) :
    Cardinal.lift.{v'} (Module.rank R M) ≤ Cardinal.lift.{v} (Module.rank R M') :=
  lift_rank_le_of_injective_injectiveₛ (RingHom.id R) f (fun _ _ h ↦ h) i f.map_smul
/-
**LinearMap.rank_le_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.rank_le_of_injective (f : M ->ₗ[R] M₁) (i : Injective f) : Modul
e.rank R M <= Module.rank R M₁
参数：f : M ->ₗ[R] M₁；i : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LinearMap.lift_rank_le_of_injective`：LinearMap.lift_rank_le_of_injective
 (f : M ->ₗ[R] M') (i : Injective f) : Cardinal.lift.{v'} (Module.rank R M) <= C
ardinal.lift.{v} (Module.…
-/
theorem LinearMap.rank_le_of_injective (f : M →ₗ[R] M₁) (i : Injective f) :
    Module.rank R M ≤ Module.rank R M₁ :=
  Cardinal.lift_le.1 (f.lift_rank_le_of_injective i)

/-- The rank of the range of a linear map is at most the rank of the source. -/
-- The proof is: a free submodule of the range lifts to a free submodule of the
-- source, by arbitrarily lifting a basis.
/-
**lift_rank_range_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_range_le (f : M ->ₗ[R] M') : Cardinal.lift.{v} (Module.rank R (L
inearMap.range f)) <= Cardinal.lift.{v'} (Module.rank R M)
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
-/
theorem lift_rank_range_le (f : M →ₗ[R] M') : Cardinal.lift.{v}
    (Module.rank R (LinearMap.range f)) ≤ Cardinal.lift.{v'} (Module.rank R M) := by
  simp only [Module.rank_def]
  rw [Cardinal.lift_iSup Cardinal.bddAbove_of_small]
  apply ciSup_le'
  rintro ⟨s, li⟩
  apply le_trans
  swap
  · apply Cardinal.lift_le.mpr
    refine le_ciSup Cardinal.bddAbove_of_small ⟨rangeSplitting f '' s, ?_⟩
    apply LinearIndependent.of_comp f.rangeRestrict
    convert! li.comp (Equiv.Set.rangeSplittingImageEquiv f s) (Equiv.injective _) using 1
  · exact (Cardinal.lift_mk_eq'.mpr ⟨Equiv.Set.rangeSplittingImageEquiv f s⟩).ge
/-
**rank_range_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_range_le (f : M ->ₗ[R] M₁) : Module.rank R (LinearMap.range f) <= Mod
ule.rank R M
参数：f : M ->ₗ[R] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_rank_range_le`：lift_rank_range_le (f : M ->ₗ[R] M') : Cardinal.lift
.{v} (Module.rank R (LinearMap.range f)) <= Cardinal.lift.{v'} (Module.rank R M)
-/
theorem rank_range_le (f : M →ₗ[R] M₁) : Module.rank R (LinearMap.range f) ≤ Module.rank R M := by
  simpa using lift_rank_range_le f
/-
**lift_rank_map_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_map_le (f : M ->ₗ[R] M') (p : Submodule R M) : Cardinal.lift.{v}
 (Module.rank R (p.map f)) <= Cardinal.lift.{v'} (Module.rank R p)
参数：f : M ->ₗ[R] M'；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lift_rank_range_le`：lift_rank_range_le (f : M ->ₗ[R] M') : Cardinal.lift
.{v} (Module.rank R (LinearMap.range f)) <= Cardinal.lift.{v'} (Module.rank R M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
-/
theorem lift_rank_map_le (f : M →ₗ[R] M') (p : Submodule R M) :
    Cardinal.lift.{v} (Module.rank R (p.map f)) ≤ Cardinal.lift.{v'} (Module.rank R p) := by
  have h := lift_rank_range_le (f.comp (Submodule.subtype p))
  rwa [LinearMap.range_comp, range_subtype] at h
/-
**rank_map_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_map_le (f : M ->ₗ[R] M₁) (p : Submodule R M) : Module.rank R (p.map f
) <= Module.rank R p
参数：f : M ->ₗ[R] M₁；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_rank_map_le`：lift_rank_map_le (f : M ->ₗ[R] M') (p : Submodule R M)
 : Cardinal.lift.{v} (Module.rank R (p.map f)) <= Cardinal.lift.{v'} (Module.ran
k R p)
-/
theorem rank_map_le (f : M →ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map f) ≤ Module.rank R p := by simpa using lift_rank_map_le f p
/-
**rank_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_map_eq {f : M ->ₗ[R] M₁} (hf : Injective f) (p : Submodule R M) : Mod
ule.rank R (p.map f) = Module.rank R p
参数：hf : Injective f；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `rank_map_le`：rank_map_le (f : M ->ₗ[R] M₁) (p : Submodule R M) : Module.
rank R (p.map f) <= Module.rank R p
· 使用定理 `LinearMap.rank_le_of_injective`：LinearMap.rank_le_of_injective (f : M ->
ₗ[R] M₁) (i : Injective f) : Module.rank R M <= Module.rank R M₁
· 使用定理 `LinearMap.submoduleMap_injective`：submoduleMap_injective [RingHomSurject
ive σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} (hf : Injective f) (p : Submodule R M) : Injective
 (f.submoduleMap p)
-/
theorem rank_map_eq {f : M →ₗ[R] M₁} (hf : Injective f) (p : Submodule R M) :
    Module.rank R (p.map f) = Module.rank R p :=
  le_antisymm (rank_map_le f p)
    ((f.submoduleMap p).rank_le_of_injective <| LinearMap.submoduleMap_injective hf p)
/-
**Submodule.rank_mono** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.rank_mono {s t : Submodule R M} (h : s <= t) : Module.rank R s <
= Module.rank R t
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.rank_le_of_injective`：LinearMap.rank_le_of_injective (f : M ->
ₗ[R] M₁) (i : Injective f) : Module.rank R M <= Module.rank R M₁
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
lemma Submodule.rank_mono {s t : Submodule R M} (h : s ≤ t) : Module.rank R s ≤ Module.rank R t :=
  (Submodule.inclusion h).rank_le_of_injective fun ⟨x, _⟩ ⟨y, _⟩ eq =>
    Subtype.ext <| show x = y from Subtype.ext_iff.1 eq

/-- Two linearly equivalent vector spaces have the same dimension, a version with different
universes. -/
/-
**LinearEquiv.lift_rank_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Cardinal.lift.{v'} (Module.ran
k R M) = Cardinal.lift.{v} (Module.rank R M')
参数：f : M ≃ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LinearMap.lift_rank_le_of_injective`：LinearMap.lift_rank_le_of_injective
 (f : M ->ₗ[R] M') (i : Injective f) : Cardinal.lift.{v'} (Module.rank R M) <= C
ardinal.lift.{v} (Module.…
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
Two linearly equivalent vector spaces have the same dimension, a version with di
fferent
universes.
-/
theorem LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') :
    Cardinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M') := by
  apply le_antisymm
  · exact f.toLinearMap.lift_rank_le_of_injective f.injective
  · exact f.symm.toLinearMap.lift_rank_le_of_injective f.symm.injective

/-- Two linearly equivalent vector spaces have the same dimension. -/
/-
**LinearEquiv.rank_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank R M = Module.rank R M₁
参数：f : M ≃ₗ[R] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')

--- 原说明 ---
Two linearly equivalent vector spaces have the same dimension.
-/
theorem LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank R M = Module.rank R M₁ :=
  Cardinal.lift_inj.1 f.lift_rank_eq
/-
**lift_rank_range_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lift_rank_range_of_injective (f : M ->ₗ[R] M') (h : Injective f) : lift.{v
} (Module.rank R (LinearMap.range f)) = lift.{v'} (Module.rank R M)
参数：f : M ->ₗ[R] M'；h : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
-/
theorem lift_rank_range_of_injective (f : M →ₗ[R] M') (h : Injective f) :
    lift.{v} (Module.rank R (LinearMap.range f)) = lift.{v'} (Module.rank R M) :=
  (LinearEquiv.ofInjective f h).lift_rank_eq.symm
/-
**rank_range_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_range_of_injective (f : M ->ₗ[R] M₁) (h : Injective f) : Module.rank 
R (LinearMap.range f) = Module.rank R M
参数：f : M ->ₗ[R] M₁；h : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
-/
theorem rank_range_of_injective (f : M →ₗ[R] M₁) (h : Injective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M :=
  (LinearEquiv.ofInjective f h).rank_eq.symm
/-
**LinearEquiv.lift_rank_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.lift_rank_map_eq (f : M ≃ₗ[R] M') (p : Submodule R M) : lift.{
v} (Module.rank R (p.map (f : M ->ₗ[R] M'))) = lift.{v'} (Module.rank R p)
参数：f : M ≃ₗ[R] M'；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
-/
theorem LinearEquiv.lift_rank_map_eq (f : M ≃ₗ[R] M') (p : Submodule R M) :
    lift.{v} (Module.rank R (p.map (f : M →ₗ[R] M'))) = lift.{v'} (Module.rank R p) :=
  (f.submoduleMap p).lift_rank_eq.symm

/-- Pushforwards of submodules along a `LinearEquiv` have the same dimension. -/
/-
**LinearEquiv.rank_map_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.rank_map_eq (f : M ≃ₗ[R] M₁) (p : Submodule R M) : Module.rank
 R (p.map (f : M ->ₗ[R] M₁)) = Module.rank R p
参数：f : M ≃ₗ[R] M₁；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁

--- 原说明 ---
Pushforwards of submodules along a `LinearEquiv` have the same dimension.
-/
theorem LinearEquiv.rank_map_eq (f : M ≃ₗ[R] M₁) (p : Submodule R M) :
    Module.rank R (p.map (f : M →ₗ[R] M₁)) = Module.rank R p :=
  (f.submoduleMap p).rank_eq.symm

variable (R M)

@[simp]
/-
**rank_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
-/
theorem rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M :=
  (LinearEquiv.ofTop ⊤ rfl).rank_eq

variable {R M}
/-
**rank_range_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_range_of_surjective (f : M ->ₗ[R] M') (h : Surjective f) : Module.ran
k R (LinearMap.range f) = Module.rank R M'
参数：f : M ->ₗ[R] M'；h : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `rank_top`：rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M
-/
theorem rank_range_of_surjective (f : M →ₗ[R] M') (h : Surjective f) :
    Module.rank R (LinearMap.range f) = Module.rank R M' := by
  rw [LinearMap.range_eq_top.2 h, rank_top]
/-
**Submodule.rank_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.rank_le (s : Submodule R M) : Module.rank R s <= Module.rank R M
参数：s : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_top`：rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem Submodule.rank_le (s : Submodule R M) : Module.rank R s ≤ Module.rank R M := by
  rw [← rank_top R M]
  exact rank_mono le_top
/-
**LinearMap.lift_rank_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.lift_rank_le_of_surjective (f : M ->ₗ[R] M') (h : Surjective f) 
: lift.{v} (Module.rank R M') <= lift.{v'} (Module.rank R M)
参数：f : M ->ₗ[R] M'；h : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_range_of_surjective`：rank_range_of_surjective (f : M ->ₗ[R] M') (h 
: Surjective f) : Module.rank R (LinearMap.range f) = Module.rank R M'
· 使用定理 `lift_rank_range_le`：lift_rank_range_le (f : M ->ₗ[R] M') : Cardinal.lift
.{v} (Module.rank R (LinearMap.range f)) <= Cardinal.lift.{v'} (Module.rank R M)
-/
theorem LinearMap.lift_rank_le_of_surjective (f : M →ₗ[R] M') (h : Surjective f) :
    lift.{v} (Module.rank R M') ≤ lift.{v'} (Module.rank R M) := by
  rw [← rank_range_of_surjective f h]
  apply lift_rank_range_le
/-
**LinearMap.rank_le_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.rank_le_of_surjective (f : M ->ₗ[R] M₁) (h : Surjective f) : Mod
ule.rank R M₁ <= Module.rank R M
参数：f : M ->ₗ[R] M₁；h : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_range_of_surjective`：rank_range_of_surjective (f : M ->ₗ[R] M') (h 
: Surjective f) : Module.rank R (LinearMap.range f) = Module.rank R M'
· 使用定理 `rank_range_le`：rank_range_le (f : M ->ₗ[R] M₁) : Module.rank R (LinearMa
p.range f) <= Module.rank R M
-/
theorem LinearMap.rank_le_of_surjective (f : M →ₗ[R] M₁) (h : Surjective f) :
    Module.rank R M₁ ≤ Module.rank R M := by
  rw [← rank_range_of_surjective f h]
  apply rank_range_le
/-
**rank_le_of_isSMulRegular** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rank_le_of_isSMulRegular {S : Type*} [CommSemiring S] [Algebra S R] [Modul
e S M] [IsScalarTower S R M] (L L' : Submodule R M) {s : S} (hr : IsSMulRegular 
M s) (h : forall x in L, s • x in L') : Module.rank R L <= Module.rank R L'
参数：L L' : Submodule R M；hr : IsSMulRegular M s；h : forall x in L, s • x in L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.rank_le_of_injective`：LinearMap.rank_le_of_injective (f : M ->
ₗ[R] M₁) (i : Injective f) : Module.rank R M <= Module.rank R M₁
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
lemma rank_le_of_isSMulRegular {S : Type*} [CommSemiring S] [Algebra S R] [Module S M]
    [IsScalarTower S R M] (L L' : Submodule R M) {s : S} (hr : IsSMulRegular M s)
    (h : ∀ x ∈ L, s • x ∈ L') :
    Module.rank R L ≤ Module.rank R L' :=
  ((Algebra.lsmul S R M s).restrict h).rank_le_of_injective <|
    fun _ _ h ↦ by simpa using hr (Subtype.ext_iff.mp h)

variable (R R' M) in
/-
**Module.rank_top_le_rank_of_isScalarTower** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.rank_top_le_rank_of_isScalarTower [Module R' M] [SMulWithZero R R']
 [IsScalarTower R R' M] [FaithfulSMul R R'] [IsScalarTower R R' R'] : Module.ran
k R' M <= Module.rank R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `LinearIndependent.restrict_scalars`：LinearIndependent.restrict_scalars [
Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] (hinj : Inject
ive fun r : R => r • (1 …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma Module.rank_top_le_rank_of_isScalarTower [Module R' M]
    [SMulWithZero R R'] [IsScalarTower R R' M] [FaithfulSMul R R'] [IsScalarTower R R' R'] :
    Module.rank R' M ≤ Module.rank R M := by
  rw [Module.rank, Module.rank]
  exact ciSup_le' fun ⟨s, hs⟩ ↦ le_ciSup_of_le Cardinal.bddAbove_of_small
    ⟨s, hs.restrict_scalars (by simpa [← faithfulSMul_iff_injective_smul_one])⟩ le_rfl

variable (R R') in
/-
**Module.lift_rank_bot_le_lift_rank_of_isScalarTower** 是 Mathlib 中的一个引理，位于命名空间 `
`。
形式化陈述：Module.lift_rank_bot_le_lift_rank_of_isScalarTower (T : Type w) [Module R 
R'] [NonAssocSemiring T] [Module R T] [Module R' T] [IsScalarTower R' T T] [Fait
hfulSMul R' T] [IsScalarTower R R' T] : Cardinal.lift.{w} (Module.rank R R') <= 
Cardinal.lift (Module.rank R T)
参数：T : Type w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.lift_rank_le_of_injective`：LinearMap.lift_rank_le_of_injective
 (f : M ->ₗ[R] M') (i : Injective f) : Cardinal.lift.{v'} (Module.rank R M) <= C
ardinal.lift.{v} (Module.…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `faithfulSMul_iff_injective_smul_one`：faithfulSMul_iff_injective_smul_one
 (R A : Type*) [MulOneClass A] [SMul R A] [IsScalarTower R A A] : FaithfulSMul R
 A ↔ Injective (fun r : R…
-/
lemma Module.lift_rank_bot_le_lift_rank_of_isScalarTower (T : Type w) [Module R R']
    [NonAssocSemiring T] [Module R T] [Module R' T] [IsScalarTower R' T T] [FaithfulSMul R' T]
    [IsScalarTower R R' T] :
    Cardinal.lift.{w} (Module.rank R R') ≤ Cardinal.lift (Module.rank R T) :=
  LinearMap.lift_rank_le_of_injective ((LinearMap.toSpanSingleton R' T 1).restrictScalars R) <|
    (faithfulSMul_iff_injective_smul_one R' T).mp ‹_›

variable (R R') in
/-
**Module.rank_bot_le_rank_of_isScalarTower** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.rank_bot_le_rank_of_isScalarTower (T : Type u') [Module R R'] [NonA
ssocSemiring T] [Module R T] [Module R' T] [IsScalarTower R' T T] [FaithfulSMul 
R' T] [IsScalarTower R R' T] : Module.rank R R' <= Module.rank R T
参数：T : Type u'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用引理 `Module.lift_rank_bot_le_lift_rank_of_isScalarTower`：Module.lift_rank_bot
_le_lift_rank_of_isScalarTower (T : Type w) [Module R R'] [NonAssocSemiring T] [
Module R T] [Module R' T] [IsScalarTower…
-/
lemma Module.rank_bot_le_rank_of_isScalarTower (T : Type u') [Module R R'] [NonAssocSemiring T]
    [Module R T] [Module R' T] [IsScalarTower R' T T] [FaithfulSMul R' T] [IsScalarTower R R' T] :
    Module.rank R R' ≤ Module.rank R T := by
  simpa using Module.lift_rank_bot_le_lift_rank_of_isScalarTower R R' T

end

end Module

