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

/-- A nontrivial Lie module is *irreducible* if its only Lie submodules are `⊥` and `⊤`. -/
/-
**LieModule.IsIrreducible** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LieModule.IsIrreducible : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nontrivial Lie module is *irreducible* if its only Lie submodules are `⊥` and 
`⊤`.
-/
abbrev LieModule.IsIrreducible : Prop :=
  IsSimpleOrder (LieSubmodule R L M)

variable {R L M} in
/-
**LieModule.IsIrreducible.mk** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieModule.IsIrreducible.mk [Nontrivial M] (h : forall N : LieSubmodule R L
 M, N != ⊥ -> N = ⊤) : IsIrreducible R L M
参数：h : forall N : LieSubmodule R L M, N != ⊥ -> N = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSimpleOrder.of_forall_eq_top`：IsSimpleOrder.of_forall_eq_top {α : Type
*} [LE α] [BoundedOrder α] [Nontrivial α] (h : forall a : α, a != ⊥ -> a = ⊤) : 
IsSimpleOrder α wher…
· 使用定理 `LieSubmodule.instNontrivial`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _ro
ot_.Module R M] […
-/
lemma LieModule.IsIrreducible.mk [Nontrivial M] (h : ∀ N : LieSubmodule R L M, N ≠ ⊥ → N = ⊤) :
    IsIrreducible R L M :=
  IsSimpleOrder.of_forall_eq_top h
/-
**LieSubmodule.eq_top_of_isIrreducible** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieSubmodule.eq_top_of_isIrreducible [LieModule.IsIrreducible R L M] (N : 
LieSubmodule R L M) [Nontrivial N] : N = ⊤
参数：N : LieSubmodule R L M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieSubmodule.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot {N : LieSubmod
ule R L M} : Nontrivial N ↔ N != ⊥
-/
lemma LieSubmodule.eq_top_of_isIrreducible [LieModule.IsIrreducible R L M]
    (N : LieSubmodule R L M) [Nontrivial N] :
    N = ⊤ :=
  (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left <| (nontrivial_iff_ne_bot R L M).mp inferInstance

namespace LieAlgebra

variable [LieAlgebra R L]

/--
A Lie algebra *has trivial radical* if its radical is trivial.
This is equivalent to having no non-trivial solvable ideals,
and further equivalent to having no non-trivial abelian ideals.

In characteristic zero, it is also equivalent to `LieAlgebra.IsSemisimple`.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
whereas we reserve it for Lie algebras that are a direct sum of simple Lie algebras.
-/
/-
**LieAlgebra.HasTrivialRadical** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：(R : Type u_1) → (L : Type u_2) → [inst : CommRing R] → [inst_1 : LieRing 
L] → [LieAlgebra R L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie algebra *has trivial radical* if its radical is trivial.
This is equivalent to having no non-trivial solvable ideals,
and further equivalent to having no non-trivial abelian ideals.

In characteristic zero, it is also equivalent to `LieAlgebra.IsSemisimple`.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#co
mment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.Has
TrivialRadical`,
whereas we reserve it for Lie algebras that are a direct sum of simple Lie algeb
ras.
-/
@[mk_iff] class HasTrivialRadical : Prop where
  radical_eq_bot : radical R L = ⊥

export HasTrivialRadical (radical_eq_bot)
attribute [simp] radical_eq_bot

/-- A Lie algebra *has central radical* if its radical coincides with its center. Such Lie algebras
are called *reductive*, if the coefficients are a field of characteristic zero.

Note that there is absolutely [no agreement](https://mathoverflow.net/questions/284713/) on what
the label 'reductive' should mean when the coefficients are not a field of characteristic zero. -/
/-
**LieAlgebra.HasCentralRadical** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：(R : Type u_1) → (L : Type u_2) → [inst : CommRing R] → [inst_1 : LieRing 
L] → [LieAlgebra R L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie algebra *has central radical* if its radical coincides with its center. Su
ch Lie algebras
are called *reductive*, if the coefficients are a field of characteristic zero.

Note that there is absolutely [no agreement](https://mathoverflow.net/questions/
284713/) on what
the label 'reductive' should mean when the coefficients are not a field of chara
cteristic zero.
-/
@[mk_iff] class HasCentralRadical : Prop where
  radical_eq_center : radical R L = center R L
/-
**LieAlgebra.hasCentralRadical_of_radical_le** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgeb
ra`。
形式化陈述：hasCentralRadical_of_radical_le (h : radical R L <= center R L) : LieAlgeb
ra.HasCentralRadical R L where radical_eq_center
参数：h : radical R L <= center R L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieAlgebra.center_le_radical`：center_le_radical : center R L <= radical 
R L
-/
lemma hasCentralRadical_of_radical_le (h : radical R L ≤ center R L) :
    LieAlgebra.HasCentralRadical R L where
  radical_eq_center := le_antisymm h (center_le_radical R L)
/-
**LieAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton L] : HasTrivialRadical R L :=
  ⟨by simpa only [radical_eq_top_of_isSolvable] using Subsingleton.elim ⊤ ⊥⟩

export HasCentralRadical (radical_eq_center)
attribute [simp] radical_eq_center

/-- A Lie algebra is simple if it is irreducible as a Lie module over itself via the adjoint
action, and it is non-Abelian. -/
/-
**LieAlgebra.IsSimple** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：(R : Type u_1) → (L : Type u_2) → [inst : CommRing R] → [inst_1 : LieRing 
L] → [LieAlgebra R L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie algebra is simple if it is irreducible as a Lie module over itself via the
 adjoint
action, and it is non-Abelian.
-/
class IsSimple : Prop where
  eq_bot_or_eq_top : ∀ I : LieIdeal R L, I = ⊥ ∨ I = ⊤
  non_abelian : ¬IsLieAbelian L

/--
A *semisimple* Lie algebra is one that is a direct sum of non-abelian atomic ideals.
These ideals are simple Lie algebras, by `LieAlgebra.IsSemisimple.isSimple_of_isAtom`.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#comment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.HasTrivialRadical`,
the weakest of the various properties which are all equivalent over a field of characteristic zero.
-/
/-
**LieAlgebra.IsSemisimple** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieAlgebra`。
形式化陈述：(R : Type u_1) → (L : Type u_2) → [inst : CommRing R] → [inst_1 : LieRing 
L] → [LieAlgebra R L] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *semisimple* Lie algebra is one that is a direct sum of non-abelian atomic ide
als.
These ideals are simple Lie algebras, by `LieAlgebra.IsSemisimple.isSimple_of_is
Atom`.

Note that the label 'semisimple' is apparently not universally agreed
[upon](https://mathoverflow.net/questions/149391/on-radicals-of-a-lie-algebra#co
mment383669_149391)
for general coefficients.

For example [Seligman, page 15](seligman1967) uses the label for `LieAlgebra.Has
TrivialRadical`,
the weakest of the various properties which are all equivalent over a field of c
haracteristic zero.
-/
class IsSemisimple : Prop where
  /-- In a semisimple Lie algebra, the supremum of the atoms is the whole Lie algebra. -/
  sSup_atoms_eq_top : sSup {I : LieIdeal R L | IsAtom I} = ⊤
  /-- In a semisimple Lie algebra, the atoms are independent. -/
  sSupIndep_isAtom : sSupIndep {I : LieIdeal R L | IsAtom I}
  /-- In a semisimple Lie algebra, the atoms are non-abelian. -/
  non_abelian_of_isAtom : ∀ I : LieIdeal R L, IsAtom I → ¬ IsLieAbelian I

end LieAlgebra

