/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Johan Commelin
-/
module

public import Mathlib.Algebra.Lie.Solvable

/-!
# Semisimple Lie algebras

In this file we define simple and semisimple Lie algebras, together with related concepts.

## Main declarations

* `LieModule.IsIrreducible`
* `LieAlgebra.IsSimple`
* `LieAlgebra.HasTrivialRadical`
* `LieAlgebra.IsSemisimple`

## Tags

lie algebra, radical, simple, semisimple
-/

public section

variable (R L M : Type*)
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M] [LieRingModule L M]

/--
Definition of `LieModule.IsIrreducible` / `LieModule.IsIrreducible` 的定义

English:
abbreviation LieModule.IsIrreducible
  signature: : Prop
  body: IsSimpleOrder (LieSubmodule R L M)

中文:
缩写 LieModule.IsIrreducible
  签名: : 命题
  定义体: IsSimpleOrder (LieSubmodule R L M)

Depends on / 依赖: IsSimpleOrder, LieSubmodule
-/
abbrev LieModule.IsIrreducible : Prop :=
  IsSimpleOrder (LieSubmodule R L M)

variable {R L M} in
/--
lemma `LieModule.IsIrreducible.mk` / 引理 `LieModule.IsIrreducible.mk`

English:
lemma LieModule.IsIrreducible.mk
  given: [Nontrivial M] (h : forall N : LieSubmodule R L M, N != ⊥ -> N = ⊤)
  proof: IsSimpleOrder.of_forall_eq_top h

中文:
引理 LieModule.IsIrreducible.mk
  条件: [Nontrivial M] (h : 对任意 N : LieSubmodule R L M, N != ⊥ -> N = ⊤)
  证明: IsSimpleOrder.of_forall_eq_top h

Depends on / 依赖: IsSimpleOrder, IsSimpleOrder.of_forall_eq_top, of_forall_eq_top
-/
lemma LieModule.IsIrreducible.mk [Nontrivial M] (h : forall N : LieSubmodule R L M, N != ⊥ -> N = ⊤) :
    IsIrreducible R L M :=
  IsSimpleOrder.of_forall_eq_top h

/--
lemma `LieSubmodule.eq_top_of_isIrreducible` / 引理 `LieSubmodule.eq_top_of_isIrreducible`

English:
lemma LieSubmodule.eq_top_of_isIrreducible
  statement: [LieModule.IsIrreducible R L M]
  proof: (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left (nontrivial_iff_ne_bot R L M).mp inferInstance

中文:
引理 LieSubmodule.eq_top_of_isIrreducible
  结论: [LieModule.IsIrreducible R L M]
  证明: (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left (nontrivial_iff_ne_bot R L M).mp inferInstance

Depends on / 依赖: IsSimpleOrder, IsSimpleOrder.eq_bot_or_eq_top, eq_bot_or_eq_top, nontrivial_iff_ne_bot, resolve_left
-/
lemma LieSubmodule.eq_top_of_isIrreducible [LieModule.IsIrreducible R L M]
    (N : LieSubmodule R L M) [Nontrivial N] :
    N = ⊤ :=
(IsSimpleOrder.eq_bot_or_eq_top N).resolve_left (nontrivial_iff_ne_bot R L M).mp inferInstance

namespace LieAlgebra

variable [LieAlgebra R L]

/--
Definition of `HasTrivialRadical` / `HasTrivialRadical` 的定义

English:
class HasTrivialRadical
  parameters: : Prop where
  axioms and operations (1):
    - radical_eq_bot : radical R L = ⊥

中文:
类 HasTrivialRadical
  参数: : 命题 where
  公理与运算 (1 个):
    - radical_eq_bot : radical R L = ⊥
-/
@[mk_iff] class HasTrivialRadical : Prop where
  radical_eq_bot : radical R L = ⊥

export HasTrivialRadical (radical_eq_bot)
attribute [simp] radical_eq_bot

/--
Definition of `HasCentralRadical` / `HasCentralRadical` 的定义

English:
class HasCentralRadical
  parameters: : Prop where
  axioms and operations (1):
    - radical_eq_center : radical R L = center R L

中文:
类 HasCentralRadical
  参数: : 命题 where
  公理与运算 (1 个):
    - radical_eq_center : radical R L = center R L
-/
@[mk_iff] class HasCentralRadical : Prop where
  radical_eq_center : radical R L = center R L

/--
lemma `hasCentralRadical_of_radical_le` / 引理 `hasCentralRadical_of_radical_le`

English:
lemma hasCentralRadical_of_radical_le
  given: (h : radical R L <= center R L)
  proof: le_antisymm h (center_le_radical R L)

中文:
引理 hasCentralRadical_of_radical_le
  条件: (h : radical R L <= center R L)
  证明: le_antisymm h (center_le_radical R L)

Depends on / 依赖: center_le_radical, le_antisymm
-/
lemma hasCentralRadical_of_radical_le (h : radical R L <= center R L) :
    LieAlgebra.HasCentralRadical R L where
  radical_eq_center := le_antisymm h (center_le_radical R L)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: L] : HasTrivialRadical R L
  body: ⟨by simpa only [radical_eq_top_of_isSolvable] using Subsingleton.elim ⊤ ⊥⟩

中文:
实例 [Subsingleton
  签名: L] : HasTrivialRadical R L
  定义体: ⟨by simpa only [radical_eq_top_of_isSolvable] using Subsingleton.elim ⊤ ⊥⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, radical_eq_top_of_isSolvable
-/
instance [Subsingleton L] : HasTrivialRadical R L :=
  ⟨by simpa only [radical_eq_top_of_isSolvable] using Subsingleton.elim ⊤ ⊥⟩

export HasCentralRadical (radical_eq_center)
attribute [simp] radical_eq_center

/--
Definition of `IsSimple` / `IsSimple` 的定义

English:
class IsSimple
  parameters: : Prop where
  axioms and operations (2):
    - eq_bot_or_eq_top : forall I : LieIdeal R L, I = ⊥ ∨ I = ⊤
    - non_abelian : ¬IsLieAbelian L

中文:
类 IsSimple
  参数: : 命题 where
  公理与运算 (2 个):
    - eq_bot_or_eq_top : 对任意 I : LieIdeal R L, I = ⊥ ∨ I = ⊤
    - non_abelian : ¬IsLieAbelian L
-/
class IsSimple : Prop where
  eq_bot_or_eq_top : forall I : LieIdeal R L, I = ⊥ ∨ I = ⊤
  non_abelian : ¬IsLieAbelian L

/--
Definition of `IsSemisimple` / `IsSemisimple` 的定义

English:
class IsSemisimple
  parameters: : Prop where
  axioms and operations (3):
    - sSup_atoms_eq_top : sSup {I : LieIdeal R L | IsAtom I} = ⊤
    - sSupIndep_isAtom : sSupIndep {I : LieIdeal R L | IsAtom I}
    - non_abelian_of_isAtom : forall I : LieIdeal R L, IsAtom I -> ¬ IsLieAbelian I

中文:
类 IsSemisimple
  参数: : 命题 where
  公理与运算 (3 个):
    - sSup_atoms_eq_top : sSup {I : LieIdeal R L | IsAtom I} = ⊤
    - sSupIndep_isAtom : sSupIndep {I : LieIdeal R L | IsAtom I}
    - non_abelian_of_isAtom : 对任意 I : LieIdeal R L, IsAtom I -> ¬ IsLieAbelian I
-/
class IsSemisimple : Prop where
  /-- In a semisimple Lie algebra, the supremum of the atoms is the whole Lie algebra. -/
  sSup_atoms_eq_top : sSup {I : LieIdeal R L | IsAtom I} = ⊤
  /-- In a semisimple Lie algebra, the atoms are independent. -/
  sSupIndep_isAtom : sSupIndep {I : LieIdeal R L | IsAtom I}
  /-- In a semisimple Lie algebra, the atoms are non-abelian. -/
  non_abelian_of_isAtom : forall I : LieIdeal R L, IsAtom I -> ¬ IsLieAbelian I

end LieAlgebra
