/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.Order.BooleanGenerators

/-!
# Semisimple Lie algebras

The famous Cartan-Dynkin-Killing classification of semisimple Lie algebras renders them one of the
most important classes of Lie algebras. In this file we prove basic results
about simple and semisimple Lie algebras.

## Main declarations

* `LieAlgebra.IsSemisimple.instHasTrivialRadical`: A semisimple Lie algebra has trivial radical.
* `LieAlgebra.IsSemisimple.instBooleanAlgebra`:
  The lattice of ideals in a semisimple Lie algebra is a Boolean algebra.
  In particular, this implies that the lattice of ideals is atomistic:
  every ideal is a direct sum of atoms (simple ideals) in a unique way.
* `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`
* `LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals`
* `LieAlgebra.abelian_radical_iff_solvable_is_abelian`

## Tags

lie algebra, radical, simple, semisimple
-/

public section

section Irreducible

variable (R L M : Type*) [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

/-
**LieModule.nontrivial_of_isIrreducible** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieModule.nontrivial_of_isIrreducible [LieModule.IsIrreducible R L M] : No
ntrivial M where exists_pair_ne
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `IsSimpleOrder.toNontrivial`：∀ {α : Type u_4} {inst : LE α} {inst_1 : Bou
ndedOrder α} [self : IsSimpleOrder α], Nontrivial α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
lemma LieModule.nontrivial_of_isIrreducible [LieModule.IsIrreducible R L M] : Nontrivial M where
  exists_pair_ne := by
    have aux : (⊥ : LieSubmodule R L M) ≠ ⊤ := bot_ne_top
    contrapose! aux
    ext m
    simpa using aux m 0

end Irreducible

namespace LieAlgebra

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

variable {R L} in
/-
**LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable** 是 Mathlib 中的一个定理，位于命名空间 `L
ieAlgebra.HasTrivialRadical`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L]   [LieAlgebra.HasTrivialRadical R L] (I : LieIdeal R L)
 [hI : LieAlgebra.IsSolvable ↥I], I = ⊥
参数：I : LieIdeal R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sSup_eq_bot`：sSup_eq_bot : sSup s = ⊥ ↔ forall a in s, a = ⊥
· 使用定理 `LieAlgebra.HasTrivialRadical.radical_eq_bot`：∀ {R : Type u_1} {L : Type 
u_2} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   [self 
: LieAlgebra.HasTrivialRadical R …
-/
theorem HasTrivialRadical.eq_bot_of_isSolvable [HasTrivialRadical R L]
    (I : LieIdeal R L) [hI : IsSolvable I] : I = ⊥ :=
  sSup_eq_bot.mp radical_eq_bot _ hI
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HasTrivialRadical R L] : LieModule.IsFaithful R L L := by
  rw [isFaithful_self_iff]
  exact HasTrivialRadical.eq_bot_of_isSolvable _

variable {R L} in
/-
**LieAlgebra.hasTrivialRadical_of_no_solvable_ideals** 是 Mathlib 中的一个定理，位于命名空间 `
LieAlgebra`。
形式化陈述：hasTrivialRadical_of_no_solvable_ideals (h : forall I : LieIdeal R L, IsSo
lvable I -> I = ⊥) : HasTrivialRadical R L
参数：h : forall I : LieIdeal R L, IsSolvable I -> I = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sSup_eq_bot`：sSup_eq_bot : sSup s = ⊥ ↔ forall a in s, a = ⊥
-/
theorem hasTrivialRadical_of_no_solvable_ideals (h : ∀ I : LieIdeal R L, IsSolvable I → I = ⊥) :
    HasTrivialRadical R L :=
  ⟨sSup_eq_bot.mpr h⟩
/-
**LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals** 是 Mathlib 中的一个定理，位于命名空间 
`LieAlgebra`。
形式化陈述：hasTrivialRadical_iff_no_solvable_ideals : HasTrivialRadical R L ↔ forall 
I : LieIdeal R L, IsSolvable I -> I = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.HasTrivialRadical.eq_bot_of_isSolvable`：∀ {R : Type u_1} {L :
 Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   
[LieAlgebra.HasTrivialRadical R L] (I :…
· 使用定理 `LieAlgebra.hasTrivialRadical_of_no_solvable_ideals`：hasTrivialRadical_of
_no_solvable_ideals (h : forall I : LieIdeal R L, IsSolvable I -> I = ⊥) : HasTr
ivialRadical R L
-/
theorem hasTrivialRadical_iff_no_solvable_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsSolvable I → I = ⊥ :=
  ⟨@HasTrivialRadical.eq_bot_of_isSolvable _ _ _ _ _, hasTrivialRadical_of_no_solvable_ideals⟩
/-
**LieAlgebra.hasTrivialRadical_iff_no_abelian_ideals** 是 Mathlib 中的一个定理，位于命名空间 `
LieAlgebra`。
形式化陈述：hasTrivialRadical_iff_no_abelian_ideals : HasTrivialRadical R L ↔ forall I
 : LieIdeal R L, IsLieAbelian I -> I = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals`：hasTrivialRadical_i
ff_no_solvable_ideals : HasTrivialRadical R L ↔ forall I : LieIdeal R L, IsSolva
ble I -> I = ⊥
· 使用定理 `LieAlgebra.ofAbelianIsSolvable`：∀ (L : Type v) [inst : LieRing L] [IsLie
Abelian L], LieAlgebra.IsSolvable L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.abelian_of_solvable_ideal_eq_bot_iff`：abelian_of_solvable_ide
al_eq_bot_iff (I : LieIdeal R L) [h : IsSolvable I] : derivedAbelianOfIdeal I = 
⊥ ↔ I = ⊥
· 使用定理 `LieAlgebra.abelian_derivedAbelianOfIdeal`：abelian_derivedAbelianOfIdeal 
(I : LieIdeal R L) : IsLieAbelian (derivedAbelianOfIdeal I)
-/
theorem hasTrivialRadical_iff_no_abelian_ideals :
    HasTrivialRadical R L ↔ ∀ I : LieIdeal R L, IsLieAbelian I → I = ⊥ := by
  rw [hasTrivialRadical_iff_no_solvable_ideals]
  constructor <;> intro h₁ I h₂
  · exact h₁ _ <| LieAlgebra.ofAbelianIsSolvable I
  · rw [← abelian_of_solvable_ideal_eq_bot_iff]
    exact h₁ _ <| abelian_derivedAbelianOfIdeal I

namespace IsSimple

variable [IsSimple R L]

/-
**LieAlgebra.IsSimple.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.IsSimple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieModule.IsIrreducible R L L := by
  suffices Nontrivial (LieIdeal R L) from ⟨IsSimple.eq_bot_or_eq_top⟩
  rw [LieSubmodule.nontrivial_iff, ← not_subsingleton_iff_nontrivial]
  have _i : ¬ IsLieAbelian L := IsSimple.non_abelian R
  contrapose _i
  infer_instance

include R in
/-- A simple lie algebra is non-trivial. -/
/-
**LieAlgebra.IsSimple.nontrivial** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.IsSimple`
。
形式化陈述：nontrivial : Nontrivial L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.IsSimple.non_abelian`：∀ (R : Type u_1) {L : Type u_2} {inst :
 CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   [self : LieAlgebra
.IsSimple R L], ¬IsLi…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
A simple lie algebra is non-trivial.
-/
lemma nontrivial : Nontrivial L := by
  have := IsSimple.non_abelian R (L := L)
  contrapose! this
  infer_instance
/-
**LieAlgebra.IsSimple.isAtom_top** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.IsSimple`
。
形式化陈述：∀ (R : Type u_1) (L : Type u_2) [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L]   [LieAlgebra.IsSimple R L], IsAtom ⊤
参数：R : Type u_1；L : Type u_2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isAtom_top`：isAtom_top : IsAtom (⊤ : α)
· 使用定理 `LieAlgebra.IsSimple.instIsIrreducible`：∀ (R : Type u_1) (L : Type u_2) [
inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAlgebra.
IsSimple R L], LieModule.Is…
-/
protected lemma isAtom_top : IsAtom (⊤ : LieIdeal R L) := isAtom_top

variable {R L} in
/-
**LieAlgebra.IsSimple.isAtom_iff_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Is
Simple`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L]   [LieAlgebra.IsSimple R L] (I : LieIdeal R L), IsAtom 
I ↔ I = ⊤
参数：I : LieIdeal R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isAtom_iff_eq_top`：isAtom_iff_eq_top {a : α} : IsAtom a ↔ a = ⊤
· 使用定理 `LieAlgebra.IsSimple.instIsIrreducible`：∀ (R : Type u_1) (L : Type u_2) [
inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAlgebra.
IsSimple R L], LieModule.Is…
-/
protected lemma isAtom_iff_eq_top (I : LieIdeal R L) : IsAtom I ↔ I = ⊤ := isAtom_iff_eq_top

variable {R L} in
/-
**LieAlgebra.IsSimple.eq_top_of_isAtom** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.IsS
imple`。
形式化陈述：eq_top_of_isAtom (I : LieIdeal R L) (hI : IsAtom I) : I = ⊤
参数：I : LieIdeal R L；hI : IsAtom I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isAtom_iff_eq_top`：isAtom_iff_eq_top {a : α} : IsAtom a ↔ a = ⊤
· 使用定理 `LieAlgebra.IsSimple.instIsIrreducible`：∀ (R : Type u_1) (L : Type u_2) [
inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAlgebra.
IsSimple R L], LieModule.Is…
-/
lemma eq_top_of_isAtom (I : LieIdeal R L) (hI : IsAtom I) : I = ⊤ := isAtom_iff_eq_top.mp hI
/-
**LieAlgebra.IsSimple.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.IsSimple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasTrivialRadical R L := by
  rw [hasTrivialRadical_iff_no_abelian_ideals]
  intro I hI
  apply (IsSimple.eq_bot_or_eq_top I).resolve_right
  rintro rfl
  rw [lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI
  exact IsSimple.non_abelian R (L := L) hI

end IsSimple

/-
**LieAlgebra.isSimple_iff_of_not_isLieAbelian** 是 Mathlib 中的一个引理，位于命名空间 `LieAlge
bra`。
形式化陈述：isSimple_iff_of_not_isLieAbelian (hL : ¬ IsLieAbelian L) : IsSimpleOrder (
LieIdeal R L) ↔ IsSimple R L
参数：hL : ¬ IsLieAbelian L。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `LieAlgebra.IsSimple.instIsIrreducible`：∀ (R : Type u_1) (L : Type u_2) [
inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieAlgebra.
IsSimple R L], LieModule.Is…
-/
lemma isSimple_iff_of_not_isLieAbelian (hL : ¬ IsLieAbelian L) :
    IsSimpleOrder (LieIdeal R L) ↔ IsSimple R L :=
  ⟨fun _ ↦ ⟨IsSimpleOrder.eq_bot_or_eq_top, hL⟩, fun _ ↦ inferInstance⟩

@[nontriviality]
/-
**LieAlgebra.not_isSimple_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`
。
形式化陈述：not_isSimple_of_subsingleton [Subsingleton L] : ¬ IsSimple R L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieAlgebra.IsSimple.non_abelian`：∀ (R : Type u_1) {L : Type u_2} {inst :
 CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   [self : LieAlgebra
.IsSimple R L], ¬IsLi…
-/
lemma not_isSimple_of_subsingleton [Subsingleton L] :
    ¬ IsSimple R L :=
  fun contra ↦ contra.non_abelian inferInstance

namespace IsSemisimple

open CompleteLattice IsCompactlyGenerated

variable {R L}
variable [IsSemisimple R L]

/-
**LieAlgebra.IsSemisimple.isSimple_of_isAtom** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgeb
ra.IsSemisimple`。
形式化陈述：isSimple_of_isAtom (I : LieIdeal R L) (hI : IsAtom I) : IsSimple R I where
 non_abelian
参数：I : LieIdeal R L；hI : IsAtom I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_singleton`：sSup_singleton {a : α} : sSup {a} = a
· 使用定理 `sSup_union`：sSup_union {s t : Set α} : sSup (s union t) = sSup s ⊔ sSup 
t
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_eq_self_of_subset_left`：union_eq_self_of_subset_left {s t : Se
t α} (h : s subseteq t) : s union t = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LieAlgebra.IsSemisimple.sSup_atoms_eq_top`：∀ {R : Type u_1} {L : Type u_
2} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   [self : 
LieAlgebra.IsSemisimple R L], s…
· 使用定理 `LieSubmodule.mem_top`：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
· 使用定理 `LieSubmodule.mem_sup`：mem_sup (x : M) : x in N ⊔ N' ↔ exists y in N, exi
sts z in N', y + z = x
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.coe_subtype`：coe_subtype : (Submodule.subtype p : p -> M) = Su
btype.val
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `lie_mem_right`：lie_mem_right (I : LieIdeal R L) (x y : L) (h : y in I) :
 ⁅x, y⁆ in I
· 使用定理 `LieSubmodule.mem_bot`：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ 
x = 0
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `LieAlgebra.IsSemisimple.sSupIndep_isAtom`：∀ {R : Type u_1} {L : Type u_2
} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   [self : L
ieAlgebra.IsSemisimple R L], s…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `lie_mem_left`：lie_mem_left (I : LieIdeal R L) (x y : L) (h : x in I) : ⁅
x, y⁆ in I
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
（共 39 条，此处仅展示前 30 条）
-/
lemma isSimple_of_isAtom (I : LieIdeal R L) (hI : IsAtom I) : IsSimple R I where
  non_abelian := IsSemisimple.non_abelian_of_isAtom I hI
  eq_bot_or_eq_top := by
    -- Suppose that `J` is an ideal of `I`.
    intro J
    -- We first show that `J` is also an ideal of the ambient Lie algebra `L`.
    let J' : LieIdeal R L :=
    { __ := J.toSubmodule.map I.incl.toLinearMap
      lie_mem := by
        rintro x _ ⟨y, hy, rfl⟩
        -- We need to show that `⁅x, y⁆ ∈ J` for any `x ∈ L` and `y ∈ J`.
        -- Since `L` is semisimple, `x` is contained
        -- in the supremum of `I` and the atoms not equal to `I`.
        have hx : x ∈ I ⊔ sSup ({I' : LieIdeal R L | IsAtom I'} \ {I}) := by
          nth_rewrite 1 [← sSup_singleton (a := I)]
          rw [← sSup_union, Set.union_sdiff_self, Set.union_eq_self_of_subset_left,
            IsSemisimple.sSup_atoms_eq_top]
          · apply LieSubmodule.mem_top
          · simp only [Set.singleton_subset_iff, Set.mem_ofPred_eq, hI]
        -- Hence we can write `x` as `a + b` with `a ∈ I`
        -- and `b` in the supremum of the atoms not equal to `I`.
        rw [LieSubmodule.mem_sup] at hx
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        -- Therefore it suffices to show that `⁅a, y⁆ ∈ J` and `⁅b, y⁆ ∈ J`.
        simp only [Submodule.carrier_eq_coe, add_lie, SetLike.mem_coe]
        apply add_mem
        -- Now `⁅a, y⁆ ∈ J` since `a ∈ I`, `y ∈ J`, and `J` is an ideal of `I`.
        · simp only [Submodule.mem_map, LieSubmodule.mem_toSubmodule, Subtype.exists]
          erw [Submodule.coe_subtype]
          simp only [exists_and_right, exists_eq_right, ha, lie_mem_left, exists_true_left]
          exact lie_mem_right R I J ⟨a, ha⟩ y hy
        -- Finally `⁅b, y⁆ = 0`, by the independence of the atoms.
        · suffices ⁅b, y.val⁆ = 0 by erw [this]; simp only [zero_mem]
          rw [← LieSubmodule.mem_bot (R := R) (L := L),
              ← (IsSemisimple.sSupIndep_isAtom hI).eq_bot]
          exact ⟨lie_mem_right R L I b y y.2, lie_mem_left _ _ _ _ _ hb⟩ }
    -- Now that we know that `J` is an ideal of `L`,
    -- we start with the proof that `I` is a simple Lie algebra.
    -- Assume that `J ≠ ⊤`.
    rw [or_iff_not_imp_right]
    intro hJ
    suffices J' = ⊥ by
      rw [eq_bot_iff] at this ⊢
      intro x hx
      suffices x ∈ J → x = 0 from this hx
      have := @this x.1
      simp only [LieIdeal.incl_coe, LieIdeal.toLieSubalgebra_toSubmodule,
        LieSubmodule.mem_mk_iff', Submodule.mem_map, LieSubmodule.mem_toSubmodule, Subtype.exists,
        LieSubmodule.mem_bot, ZeroMemClass.coe_eq_zero, forall_exists_index, and_imp, J'] at this
      exact fun _ ↦ this (↑x) x.property hx rfl
    -- We need to show that `J = ⊥`.
    -- Since `J` is an ideal of `L`, and `I` is an atom,
    -- it suffices to show that `J < I`.
    apply hI.2
    rw [lt_iff_le_and_ne]
    constructor
    -- We know that `J ≤ I` since `J` is an ideal of `I`.
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    -- So we need to show `J ≠ I` as ideals of `L`.
    -- This follows from our assumption that `J ≠ ⊤` as ideals of `I`.
    contrapose hJ
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    rw [← hJ] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact hy

set_option backward.isDefEq.respectTransparency false in
/--
In a semisimple Lie algebra,
Lie ideals that are contained in the supremum of a finite collection of atoms
are themselves the supremum of a finite subcollection of those atoms.

By a compactness argument, this statement can be extended to arbitrary sets of atoms.
See `atomistic`.

The proof is by induction on the finite set of atoms.
-/
private
/-
**LieAlgebra.IsSemisimple.finitelyAtomistic** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebr
a.IsSemisimple`。
形式化陈述：finitelyAtomistic : forall s : Finset (LieIdeal R L), ↑s subseteq {I : Lie
Ideal R L | IsAtom I} -> forall I : LieIdeal R L, I <= s.sup id -> exists t subs
eteq s, I = t.sup id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma finitelyAtomistic : ∀ s : Finset (LieIdeal R L), ↑s ⊆ {I : LieIdeal R L | IsAtom I} →
    ∀ I : LieIdeal R L, I ≤ s.sup id → ∃ t ⊆ s, I = t.sup id := by
  intro s hs I hI
  let S := {I : LieIdeal R L | IsAtom I}
  obtain rfl | hI := hI.eq_or_lt
  · exact ⟨s, Finset.Subset.rfl, rfl⟩
  -- We assume that `I` is strictly smaller than the supremum of `s`.
  -- Hence there must exist an atom `J` that is not contained in `I`.
  obtain ⟨J, hJs, hJI⟩ : ∃ J ∈ s, ¬ J ≤ I := by
    by_contra! H
    exact hI.ne (le_antisymm hI.le (s.sup_le H))
  classical
  let s' := s.erase J
  have hs' : s' ⊂ s := Finset.erase_ssubset hJs
  have hs'S : ↑s' ⊆ S := Set.Subset.trans (Finset.coe_subset.mpr hs'.subset) hs
  -- If we show that `I` is contained in the supremum `K` of the complement of `J` in `s`,
  -- then we are done by recursion.
  set K := s'.sup id
  suffices I ≤ K by
    obtain ⟨t, hts', htI⟩ := finitelyAtomistic s' hs'S I this
    exact ⟨t, hts'.trans hs'.subset, htI⟩
  -- Since `I` is contained in the supremum of `J` with the supremum of `s'`,
  -- any element `x` of `I` can be written as `y + z` for some `y ∈ J` and `z ∈ K`.
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ : ∃ y ∈ id J, ∃ z ∈ K, y + z = x := by
    rw [← LieSubmodule.mem_sup, ← Finset.sup_insert, Finset.insert_erase hJs]
    exact hI.le hx
  -- If we show that `y` is contained in the center of `J`,
  -- then we find `x = z`, and hence `x` is contained in the supremum of `s'`.
  -- Since `x` was arbitrary, we have shown that `I` is contained in the supremum of `s'`.
  suffices ⟨y, hy⟩ ∈ LieAlgebra.center R J by
    have _inst := isSimple_of_isAtom J (hs hJs)
    simp_all
  -- To show that `y` is in the center of `J`,
  -- we show that any `j ∈ J` brackets to `0` with `z` and with `x = y + z`.
  -- By a simple computation, that implies `⁅j, y⁆ = 0`, for all `j`, as desired.
  intro j
  suffices ⁅(j : L), z⁆ = 0 ∧ ⁅(j : L), y + z⁆ = 0 by
    rw [lie_add, this.1, add_zero] at this
    ext
    exact this.2
  rw [← LieSubmodule.mem_bot (R := R) (L := L), ← LieSubmodule.mem_bot (R := R) (L := L)]
  constructor
  -- `j` brackets to `0` with `z`, since `⁅j, z⁆` is contained in `⁅J, K⁆ ≤ J ⊓ K`,
  -- and `J ⊓ K = ⊥` by the independence of the atoms.
  · apply (sSupIndep_isAtom.disjoint_sSup (hs hJs) hs'S (Finset.notMem_erase _ _)).le_bot
    apply LieSubmodule.lie_le_inf
    apply LieSubmodule.lie_mem_lie j.2
    simpa only [K, Finset.sup_id_eq_sSup] using hz
  -- By similar reasoning, `j` brackets to `0` with `x = y + z ∈ I`, if we show `J ⊓ I = ⊥`.
  suffices J ⊓ I = ⊥ by
    apply this.le
    apply LieSubmodule.lie_le_inf
    exact LieSubmodule.lie_mem_lie j.2 hx
  -- Indeed `J ⊓ I = ⊥`, since `J` is an atom that is not contained in `I`.
  apply ((hs hJs).le_iff.mp _).resolve_right
  · contrapose hJI
    rw [← hJI]
    exact inf_le_right
  exact inf_le_left
termination_by s => s.card
decreasing_by exact Finset.card_lt_card hs'

variable (R L) in
/-
**LieAlgebra.IsSemisimple.booleanGenerators** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebr
a.IsSemisimple`。
形式化陈述：booleanGenerators : BooleanGenerators {I : LieIdeal R L | IsAtom I} where 
isAtom _ hI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Lie.Semisimple.Basic.0.LieAlgebra.IsSemisimple.
finitelyAtomistic`：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 :
 LieRing L] [inst_2 : LieAlgebra R L]   [LieAlgebra.IsSemisimple R L] (s : Fins…
-/
lemma booleanGenerators : BooleanGenerators {I : LieIdeal R L | IsAtom I} where
  isAtom _ hI := hI
  finitelyAtomistic _ _ hs _ hIs := finitelyAtomistic _ hs _ hIs
/-
**LieAlgebra.IsSemisimple.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.IsSemisimple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instDistribLattice : DistribLattice (LieIdeal R L) :=
  (booleanGenerators R L).distribLatticeOfSSupEqTop sSup_atoms_eq_top

noncomputable
/-
**LieAlgebra.IsSemisimple.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.IsSemisimple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instBooleanAlgebra : BooleanAlgebra (LieIdeal R L) :=
  (booleanGenerators R L).booleanAlgebraOfSSupEqTop sSup_atoms_eq_top

/-- A semisimple Lie algebra has trivial radical. -/
/-
**LieAlgebra.IsSemisimple.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.IsSemisimple`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semisimple Lie algebra has trivial radical.
-/
instance (priority := 100) instHasTrivialRadical : HasTrivialRadical R L := by
  rw [hasTrivialRadical_iff_no_abelian_ideals]
  intro I hI
  apply (eq_bot_or_exists_atom_le I).resolve_right
  rintro ⟨J, hJ, hJ'⟩
  apply IsSemisimple.non_abelian_of_isAtom J hJ
  constructor
  intro x y
  ext
  simp only [LieIdeal.coe_bracket_of_module, LieSubmodule.coe_bracket, ZeroMemClass.coe_zero]
  have : (⁅(⟨x, hJ' x.2⟩ : I), ⟨y, hJ' y.2⟩⁆ : I) = 0 := trivial_lie_zero _ _ _ _
  apply_fun Subtype.val at this
  exact this

end IsSemisimple

/-- A simple Lie algebra is semisimple. -/
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simple Lie algebra is semisimple.
-/
instance (priority := 100) IsSimple.instIsSemisimple [IsSimple R L] :
    IsSemisimple R L := by
  constructor
  · simp
  · simpa using sSupIndep_singleton _
  · intro I hI₁ hI₂
    apply IsSimple.non_abelian (R := R) (L := L)
    rw [IsSimple.isAtom_iff_eq_top] at hI₁
    rwa [hI₁, lie_abelian_iff_equiv_lie_abelian LieIdeal.topEquiv] at hI₂

/-- An abelian Lie algebra with trivial radical is trivial. -/
/-
**LieAlgebra.subsingleton_of_hasTrivialRadical_lie_abelian** 是 Mathlib 中的一个定理，位于
命名空间 `LieAlgebra`。
形式化陈述：subsingleton_of_hasTrivialRadical_lie_abelian [HasTrivialRadical R L] [h :
 IsLieAbelian L] : Subsingleton L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieSubmodule.subsingleton_iff`：subsingleton_iff : Subsingleton (LieSubmo
dule R L M) ↔ Subsingleton M
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.center_eq_bot`：center_eq_bot [LieModule.IsFaithful R L L] : c
enter R L = ⊥
· 使用定理 `LieAlgebra.instIsFaithfulOfHasTrivialRadical`：∀ (R : Type u_1) (L : Type
 u_2) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieA
lgebra.HasTrivialRadical R L], Lie…
· 使用定理 `LieAlgebra.isLieAbelian_iff_center_eq_top`：isLieAbelian_iff_center_eq_to
p : IsLieAbelian L ↔ center R L = ⊤

--- 原说明 ---
An abelian Lie algebra with trivial radical is trivial.
-/
theorem subsingleton_of_hasTrivialRadical_lie_abelian [HasTrivialRadical R L] [h : IsLieAbelian L] :
    Subsingleton L := by
  rw [isLieAbelian_iff_center_eq_top R L, center_eq_bot] at h
  exact (LieSubmodule.subsingleton_iff R L L).mp (subsingleton_of_bot_eq_top h)
/-
**LieAlgebra.abelian_radical_of_hasTrivialRadical** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Algebra`。
形式化陈述：abelian_radical_of_hasTrivialRadical [HasTrivialRadical R L] : IsLieAbelia
n (radical R L)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.HasTrivialRadical.radical_eq_bot`：∀ {R : Type u_1} {L : Type 
u_2} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   [self 
: LieAlgebra.HasTrivialRadical R …
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem abelian_radical_of_hasTrivialRadical [HasTrivialRadical R L] :
    IsLieAbelian (radical R L) := by
  rw [HasTrivialRadical.radical_eq_bot]; exact LieIdeal.isLieAbelian_of_trivial ..
/-
**LieAlgebra.abelian_radical_iff_solvable_is_abelian** 是 Mathlib 中的一个定理，位于命名空间 `
LieAlgebra`。
形式化陈述：abelian_radical_iff_solvable_is_abelian [IsNoetherian R L] : IsLieAbelian 
(radical R L) ↔ forall I : LieIdeal R L, IsSolvable I -> IsLieAbelian I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `Function.Injective.isLieAbelian`：Function.Injective.isLieAbelian {R : Ty
pe u} {L₁ : Type v} {L₂ : Type w} [CommRing R] [LieRing L₁] [LieRing L₂] [LieAlg
ebra R L₁] [LieAlgebr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.LieIdeal.solvable_iff_le_radical`：∀ (R : Type u) (L : Type v)
 [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] [IsNoetheria
n R L]   (I : LieIdeal R L), LieA…
· 使用定理 `LieIdeal.inclusion_injective`：inclusion_injective {I₁ I₂ : LieIdeal R L}
 (h : I₁ <= I₂) : Function.Injective (inclusion h)
-/
theorem abelian_radical_iff_solvable_is_abelian [IsNoetherian R L] :
    IsLieAbelian (radical R L) ↔ ∀ I : LieIdeal R L, IsSolvable I → IsLieAbelian I := by
  constructor
  · rintro h₁ I h₂
    rw [LieIdeal.solvable_iff_le_radical] at h₂
    exact (LieIdeal.inclusion_injective h₂).isLieAbelian h₁
  · intro h; apply h; infer_instance

attribute [local instance 100] LieRing.ofAssociativeRing
/-
**LieAlgebra.ad_ker_eq_bot_of_hasTrivialRadical** 是 Mathlib 中的一个定理，位于命名空间 `LieAl
gebra`。
形式化陈述：ad_ker_eq_bot_of_hasTrivialRadical [HasTrivialRadical R L] : (ad R L).ker 
= ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.ker_eq_bot`：∀ (R : Type u) (L : Type v) (M : Type w) [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGro
up M] [ins…
· 使用定理 `LieAlgebra.instIsFaithfulOfHasTrivialRadical`：∀ (R : Type u_1) (L : Type
 u_2) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [LieA
lgebra.HasTrivialRadical R L], Lie…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ad_ker_eq_bot_of_hasTrivialRadical [HasTrivialRadical R L] : (ad R L).ker = ⊥ := by simp

end LieAlgebra

