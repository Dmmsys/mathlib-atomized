/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kevin Buzzard
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Noetherian rings and modules

The following are equivalent for a module M over a ring R:
1. Every increasing chain of submodules M₁ ⊆ M₂ ⊆ M₃ ⊆ ⋯ eventually stabilises.
2. Every submodule is finitely generated.

A module satisfying these equivalent conditions is said to be a *Noetherian* R-module.
A ring is a *Noetherian ring* if it is Noetherian as a module over itself.

(Note that we do not assume yet that our rings are commutative,
so perhaps this should be called "left-Noetherian".
To avoid cumbersome names once we specialize to the commutative case,
we don't make this explicit in the declaration names.)

## Main definitions

Let `R` be a ring and let `M` and `P` be `R`-modules. Let `N` be an `R`-submodule of `M`.

* `IsNoetherian R M` is the proposition that `M` is a Noetherian `R`-module. It is a class,
  implemented as the predicate that all `R`-submodules of `M` are finitely generated.

## Main statements

* `isNoetherian_iff` is the theorem that an R-module M is Noetherian iff `>` is well-founded on
  `Submodule R M`.

Note that the Hilbert basis theorem, that if a commutative ring R is Noetherian then so is R[X],
is proved in `RingTheory.Polynomial`.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Noetherian, noetherian, Noetherian ring, Noetherian module, noetherian ring, noetherian module

-/

@[expose] public section

assert_not_exists Finsupp.linearCombination Matrix Pi.basis

open Set Pointwise

/-- `IsNoetherian R M` is the proposition that `M` is a Noetherian `R`-module,
implemented as the predicate that all `R`-submodules of `M` are finitely generated.
-/
-- TODO: should this be renamed to `Noetherian`?
/-
**IsNoetherian** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → (M : Type u_2) → [inst : Semiring R] → [inst_1 : AddCommM
onoid M] → [_root_.Module R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class IsNoetherian (R M) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where
  noetherian : ∀ s : Submodule R M, s.FG

attribute [inherit_doc IsNoetherian] IsNoetherian.noetherian

section

variable {R : Type*} {M : Type*} {P : Type*}
variable [Semiring R] [AddCommMonoid M] [AddCommMonoid P]
variable [Module R M] [Module R P]

open IsNoetherian

/-- An R-module is Noetherian iff all its submodules are finitely-generated. -/
/-
**isNoetherian_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_def : IsNoetherian R M ↔ forall s : Submodule R M, s.FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…

--- 原说明 ---
An R-module is Noetherian iff all its submodules are finitely-generated.
-/
theorem isNoetherian_def : IsNoetherian R M ↔ ∀ s : Submodule R M, s.FG :=
  ⟨fun h => h.noetherian, IsNoetherian.mk⟩
/-
**isNoetherian_submodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_submodule {N : Submodule R M} : IsNoetherian R N ↔ forall s :
 Submodule R M, s <= N -> s.FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Submodule.map_comap_eq_self`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type 
u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddC
ommMonoid M] [ins…
· 使用定理 `Submodule.fg_of_fg_map_injective`：fg_of_fg_map_injective (hf : Function.
Injective f) {N : Submodule R M} (hfn : (N.map f).FG) : N.FG
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Submodule.map_subtype_le`：map_subtype_le (p' : Submodule R p) : map p.su
btype p' <= p
-/
theorem isNoetherian_submodule {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, s ≤ N → s.FG := by
  refine ⟨fun ⟨hn⟩ => fun s hs =>
    have : s ≤ LinearMap.range N.subtype := N.range_subtype.symm ▸ hs
    Submodule.map_comap_eq_self this ▸ (hn _).map _,
    fun h => ⟨fun s => ?_⟩⟩
  specialize h (s.map N.subtype) (Submodule.map_subtype_le N s)
  exact Submodule.fg_of_fg_map_injective N.subtype Subtype.val_injective h
/-
**isNoetherian_submodule_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_submodule_left {N : Submodule R M} : IsNoetherian R N ↔ foral
l s : Submodule R M, (N ⊓ s).FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isNoetherian_submodule`：isNoetherian_submodule {N : Submodule R M} : IsN
oetherian R N ↔ forall s : Submodule R M, s <= N -> s.FG
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
-/
theorem isNoetherian_submodule_left {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, (N ⊓ s).FG :=
  isNoetherian_submodule.trans ⟨fun H _ => H _ inf_le_left, fun H _ hs => inf_of_le_right hs ▸ H _⟩
/-
**isNoetherian_submodule_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_submodule_right {N : Submodule R M} : IsNoetherian R N ↔ fora
ll s : Submodule R M, (s ⊓ N).FG
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isNoetherian_submodule`：isNoetherian_submodule {N : Submodule R M} : IsN
oetherian R N ↔ forall s : Submodule R M, s <= N -> s.FG
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
-/
theorem isNoetherian_submodule_right {N : Submodule R M} :
    IsNoetherian R N ↔ ∀ s : Submodule R M, (s ⊓ N).FG :=
  isNoetherian_submodule.trans ⟨fun H _ => H _ inf_le_right, fun H _ hs => inf_of_le_left hs ▸ H _⟩
/-
**isNoetherian_submodule'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isNoetherian_submodule' [IsNoetherian R M] (N : Submodule R M) : IsNoether
ian R N
参数：N : Submodule R M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isNoetherian_submodule`：isNoetherian_submodule {N : Submodule R M} : IsN
oetherian R N ↔ forall s : Submodule R M, s <= N -> s.FG
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
-/
instance isNoetherian_submodule' [IsNoetherian R M] (N : Submodule R M) : IsNoetherian R N :=
  isNoetherian_submodule.2 fun _ _ => IsNoetherian.noetherian _
/-
**isNoetherian_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_of_le {s t : Submodule R M} [ht : IsNoetherian R t] (h : s <=
 t) : IsNoetherian R s
参数：h : s <= t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isNoetherian_submodule`：isNoetherian_submodule {N : Submodule R M} : IsN
oetherian R N ↔ forall s : Submodule R M, s <= N -> s.FG
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem isNoetherian_of_le {s t : Submodule R M} [ht : IsNoetherian R t] (h : s ≤ t) :
    IsNoetherian R s :=
  isNoetherian_submodule.mpr fun _ hs' => isNoetherian_submodule.mp ht _ (le_trans hs' h)

end

open IsNoetherian Submodule Function

section

universe w

variable {R M P : Type*} {N : Type w} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P]

/-
**isNoetherian_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_iff' : IsNoetherian R M ↔ WellFoundedGT (Submodule R M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_iff_compact`：fg_iff_compact (s : Submodule R M) : s.FG ↔ Is
CompactElement s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `CompleteLattice.wellFoundedGT_characterisations`：wellFoundedGT_character
isations : List.TFAE [WellFoundedGT α, IsSupFiniteCompact α, IsSupClosedCompact 
α, forall k : α, IsCompactElement k]
-/
theorem isNoetherian_iff' : IsNoetherian R M ↔ WellFoundedGT (Submodule R M) := by
  refine .trans ?_ ((CompleteLattice.wellFoundedGT_characterisations <| Submodule R M).out 0 3).symm
  exact
    ⟨fun ⟨h⟩ => fun k => (fg_iff_compact k).mp (h k), fun h =>
      ⟨fun k => (fg_iff_compact k).mpr (h k)⟩⟩
/-
**isNoetherian_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_iff : IsNoetherian R M ↔ WellFounded ((· > ·) : Submodule R M
 -> Submodule R M -> Prop)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isNoetherian_iff'`：isNoetherian_iff' : IsNoetherian R M ↔ WellFoundedGT 
(Submodule R M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isWellFounded_iff`：∀ (α : Type u) (r : α → α → Prop), IsWellFounded α r 
↔ WellFounded r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isNoetherian_iff :
    IsNoetherian R M ↔ WellFounded ((· > ·) : Submodule R M → Submodule R M → Prop) := by
  rw [isNoetherian_iff', ← isWellFounded_iff]

alias ⟨IsNoetherian.wf, _⟩ := isNoetherian_iff

alias ⟨IsNoetherian.wellFoundedGT, isNoetherian_mk⟩ := isNoetherian_iff'
/-
**wellFoundedGT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：wellFoundedGT [h : IsNoetherian R M] : WellFoundedGT (Submodule R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.wellFoundedGT`：∀ {R : Type u_1} {M : Type u_2} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   IsNoetherian 
R M → WellFounde…
-/
instance wellFoundedGT [h : IsNoetherian R M] : WellFoundedGT (Submodule R M) :=
  h.wellFoundedGT
/-
**isNoetherian_iff_fg_wellFounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherian_iff_fg_wellFounded : IsNoetherian R M ↔ WellFoundedGT { N : S
ubmodule R M // N.FG }
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.wellFoundedLT`：∀ {α : Type u_2} {β : Type u_3} [inst : Pr
eorder α] [inst_1 : Preorder β] [WellFoundedLT β] (f : α ↪o β),   WellFoundedLT 
α
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Submodule.FG.sup`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N₁ N₂ : Submodule R M},
 N₁.FG…
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
-/
theorem isNoetherian_iff_fg_wellFounded :
    IsNoetherian R M ↔ WellFoundedGT { N : Submodule R M // N.FG } := by
  let α := { N : Submodule R M // N.FG }
  constructor
  · intro H
    let f : α ↪o Submodule R M := OrderEmbedding.subtype _
    exact OrderEmbedding.wellFoundedLT f.dual
  · intro H
    constructor
    intro N
    obtain ⟨⟨N₀, h₁⟩, e : N₀ ≤ N, h₂⟩ :=
      WellFounded.has_min H.wf { N' : α | N'.1 ≤ N } ⟨⟨⊥, Submodule.fg_bot⟩, @bot_le _ _ _ N⟩
    convert! h₁
    refine (e.antisymm ?_).symm
    by_contra h₃
    obtain ⟨x, hx₁ : x ∈ N, hx₂ : x ∉ N₀⟩ := Set.not_subset.mp h₃
    apply hx₂
    rw [eq_of_le_of_not_lt (le_sup_right : N₀ ≤ _) (h₂
      ⟨_, Submodule.FG.sup ⟨{x}, by rw [Finset.coe_singleton]⟩ h₁⟩ <|
      sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) e)]
    exact (le_sup_left : R ∙ x ≤ _) (Submodule.mem_span_singleton_self _)

/-- A module is Noetherian iff every nonempty set of submodules has a maximal submodule among them.
-/
/-
**set_has_maximal_iff_noetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：set_has_maximal_iff_noetherian : (forall a : Set <| Submodule R M, a.Nonem
pty -> exists M' in a, forall I in a, ¬M' < I) ↔ IsNoetherian R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isNoetherian_iff`：isNoetherian_iff : IsNoetherian R M ↔ WellFounded ((· 
> ·) : Submodule R M -> Submodule R M -> Prop)
· 使用定理 `WellFounded.wellFounded_iff_has_min`：wellFounded_iff_has_min {r : α -> α
 -> Prop} : WellFounded r ↔ forall s : Set α, s.Nonempty -> exists m in s, foral
l x in s, ¬r x m
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A module is Noetherian iff every nonempty set of submodules has a maximal submod
ule among them.
-/
theorem set_has_maximal_iff_noetherian :
    (∀ a : Set <| Submodule R M, a.Nonempty → ∃ M' ∈ a, ∀ I ∈ a, ¬M' < I) ↔ IsNoetherian R M := by
  rw [isNoetherian_iff, WellFounded.wellFounded_iff_has_min]

/-- A module is Noetherian iff every increasing chain of submodules stabilizes. -/
/-
**monotone_stabilizes_iff_noetherian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_stabilizes_iff_noetherian : (forall f : Nat ->o Submodule R M, ex
ists n, forall m, n <= m -> f n = f m) ↔ IsNoetherian R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isNoetherian_iff'`：isNoetherian_iff' : IsNoetherian R M ↔ WellFoundedGT 
(Submodule R M)
· 使用定理 `wellFoundedGT_iff_monotone_chain_condition`：wellFoundedGT_iff_monotone_c
hain_condition [PartialOrder α] : WellFoundedGT α ↔ forall a : Nat ->o α, exists
 n, forall m, n <= m -> a n = a …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A module is Noetherian iff every increasing chain of submodules stabilizes.
-/
theorem monotone_stabilizes_iff_noetherian :
    (∀ f : ℕ →o Submodule R M, ∃ n, ∀ m, n ≤ m → f n = f m) ↔ IsNoetherian R M := by
  rw [isNoetherian_iff', wellFoundedGT_iff_monotone_chain_condition]

variable [IsNoetherian R M]

open Filter
/-- For an endomorphism of a Noetherian module, any sufficiently large iterate has disjoint kernel
and range. -/
/-
**Module.End.eventually_disjoint_ker_pow_range_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.End.eventually_disjoint_ker_pow_range_pow (f : End R M) : forallᶠ n
 in atTop, Disjoint (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n))
参数：f : End R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_stabilizes_iff_noetherian`：monotone_stabilizes_iff_noetherian :
 (forall f : Nat ->o Submodule R M, exists n, forall m, n <= m -> f n = f m) ↔ I
sNoetherian R M
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Module.End.pow_map_zero_of_le`：pow_map_zero_of_le {f : End R M} {m : M} 
{k l : Nat} (hk : k <= l) (hm : (f ^ k) m = 0) : (f ^ l) m = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.End.pow_apply`：pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n
) m = f^[n] m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k

--- 原说明 ---
For an endomorphism of a Noetherian module, any sufficiently large iterate has d
isjoint kernel
and range.
-/
theorem Module.End.eventually_disjoint_ker_pow_range_pow (f : End R M) :
    ∀ᶠ n in atTop, Disjoint (LinearMap.ker (f ^ n)) (LinearMap.range (f ^ n)) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → LinearMap.ker (f ^ n) = LinearMap.ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine eventually_atTop.mpr ⟨n, fun m hm ↦ disjoint_iff.mpr ?_⟩
  rw [← hn _ hm, Submodule.eq_bot_iff]
  rintro - ⟨hx, ⟨x, rfl⟩⟩
  apply pow_map_zero_of_le hm
  replace hx : x ∈ LinearMap.ker (f ^ (n + m)) := by
    simpa [f.pow_apply n, f.pow_apply m, ← f.pow_apply (n + m), ← iterate_add_apply] using hx
  rwa [← hn _ (n.le_add_right m)] at hx
/-
**LinearMap.eventually_iSup_ker_pow_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.eventually_iSup_ker_pow_eq (f : M ->ₗ[R] M) : forallᶠ n in atTop
, ⨆ m, LinearMap.ker (f ^ m) = LinearMap.ker (f ^ n)
参数：f : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotone_stabilizes_iff_noetherian`：monotone_stabilizes_iff_noetherian :
 (forall f : Nat ->o Submodule R M, exists n, forall m, n <= m -> f n = f m) ↔ I
sNoetherian R M
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma LinearMap.eventually_iSup_ker_pow_eq (f : M →ₗ[R] M) :
    ∀ᶠ n in atTop, ⨆ m, LinearMap.ker (f ^ m) = LinearMap.ker (f ^ n) := by
  obtain ⟨n, hn : ∀ m, n ≤ m → ker (f ^ n) = ker (f ^ m)⟩ :=
    monotone_stabilizes_iff_noetherian.mpr inferInstance f.iterateKer
  refine eventually_atTop.mpr ⟨n, fun m hm ↦ ?_⟩
  refine le_antisymm (iSup_le fun l ↦ ?_) (le_iSup (fun i ↦ LinearMap.ker (f ^ i)) m)
  rcases le_or_gt m l with h | h
  · rw [← hn _ (hm.trans h), hn _ hm]
  · exact f.iterateKer.monotone h.le

end

/-- A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated. -/
@[wikidata Q582271]
/-
**IsNoetherianRing** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：IsNoetherianRing (R) [Semiring R]
参数：R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A (semi)ring is Noetherian if it is Noetherian as a module over itself,
i.e. all its ideals are finitely generated.
-/
abbrev IsNoetherianRing (R) [Semiring R] :=
  IsNoetherian R R
/-
**isNoetherianRing_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherianRing_iff {R} [Semiring R] : IsNoetherianRing R ↔ IsNoetherian 
R R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isNoetherianRing_iff {R} [Semiring R] : IsNoetherianRing R ↔ IsNoetherian R R :=
  Iff.rfl

/-- A ring is Noetherian if and only if all its ideals are finitely-generated. -/
/-
**isNoetherianRing_iff_ideal_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isNoetherianRing_iff_ideal_fg (R : Type*) [Semiring R] : IsNoetherianRing 
R ↔ forall I : Ideal R, I.FG
参数：R : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isNoetherianRing_iff`：isNoetherianRing_iff {R} [Semiring R] : IsNoetheri
anRing R ↔ IsNoetherian R R
· 使用定理 `isNoetherian_def`：isNoetherian_def : IsNoetherian R M ↔ forall s : Submo
dule R M, s.FG

--- 原说明 ---
A ring is Noetherian if and only if all its ideals are finitely-generated.
-/
theorem isNoetherianRing_iff_ideal_fg (R : Type*) [Semiring R] :
    IsNoetherianRing R ↔ ∀ I : Ideal R, I.FG :=
  isNoetherianRing_iff.trans isNoetherian_def
/-
**Ideal.fg_of_isNoetherianRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.fg_of_isNoetherianRing {R : Type*} [Semiring R] [IsNoetherianRing R]
 (I : Ideal R) : I.FG
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
-/
lemma Ideal.fg_of_isNoetherianRing {R : Type*} [Semiring R] [IsNoetherianRing R] (I : Ideal R) :
    I.FG :=
  IsNoetherian.noetherian _

alias Ideal.FG.of_isNoetherianRing := Ideal.fg_of_isNoetherianRing
