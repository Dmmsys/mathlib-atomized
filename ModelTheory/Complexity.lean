/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Equivalence

/-!
# Quantifier Complexity

This file defines quantifier complexity of first-order formulas, and constructs prenex normal forms.

## Main Definitions

- `FirstOrder.Language.BoundedFormula.IsAtomic` defines atomic formulas - those which are
  constructed only from terms and relations.
- `FirstOrder.Language.BoundedFormula.IsQF` defines quantifier-free formulas - those which are
  constructed only from atomic formulas and Boolean operations.
- `FirstOrder.Language.BoundedFormula.IsPrenex` defines when a formula is in prenex normal form -
  when it consists of a series of quantifiers applied to a quantifier-free formula.
- `FirstOrder.Language.BoundedFormula.toPrenex` constructs a prenex normal form of a given formula.


## Main Results

- `FirstOrder.Language.BoundedFormula.realize_toPrenex` shows that the prenex normal form of a
  formula has the same realization as the original formula.

-/

@[expose] public section

universe u v w u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {α : Type u'} {β : Type v'}
variable {n l : Nat} {φ : L.BoundedFormula α l}

open FirstOrder Structure Fin

namespace BoundedFormula

/--
Inductive type `IsAtomic` / 归纳类型 `IsAtomic`

English:
inductive IsAtomic
  parameters: : L.BoundedFormula α n -> Prop
  constructors (2):
    - equal: (t₁ t₂ : L.Term (α oplus (Fin n))) : IsAtomic (t₁.bdEqual t₂)
    - rel: {l : Nat} (R : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n))) : IsAtomic (R.boundedFormula ts)

中文:
归纳类型 是原子的
  参数: : L.BoundedFormula α n -> 命题
  构造子 (2 个):
    - equal: (t₁ t₂ : L.项 (α oplus (有限集 n))) : 是原子的 (t₁.bdEqual t₂)
    - rel: {l : 自然数} (R : L.关系 l) (ts : 有限集 l -> L.项 (α oplus (有限集 n))) : 是原子的 (R.boundedFormula ts)
-/
inductive IsAtomic : L.BoundedFormula α n -> Prop
  | equal (t₁ t₂ : L.Term (α oplus (Fin n))) : IsAtomic (t₁.bdEqual t₂)
  | rel {l : Nat} (R : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n))) :
    IsAtomic (R.boundedFormula ts)

/--
theorem `not_all_isAtomic` / 定理 `not_all_isAtomic`

English:
theorem not_all_isAtomic
  given: (φ : L.BoundedFormula α (n + 1))
  statement: ¬φ.all.IsAtomic
  proof: fun con => by
  cases con

中文:
定理 not_all_isAtomic
  条件: (φ : L.BoundedFormula α (n + 1))
  结论: ¬φ.all.是原子的
  证明: fun con => by
  cases con
-/
theorem not_all_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsAtomic := fun con => by
  cases con

/--
theorem `not_ex_isAtomic` / 定理 `not_ex_isAtomic`

English:
theorem not_ex_isAtomic
  given: (φ : L.BoundedFormula α (n + 1))
  statement: ¬φ.ex.IsAtomic
  proof: fun con => by cases con

中文:
定理 not_ex_isAtomic
  条件: (φ : L.BoundedFormula α (n + 1))
  结论: ¬φ.ex.是原子的
  证明: fun con => by cases con
-/
theorem not_ex_isAtomic (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsAtomic := fun con => by cases con

/--
theorem `IsAtomic.relabel` / 定理 `IsAtomic.relabel`

English:
theorem IsAtomic.relabel
  statement: {m : Nat} {φ : L.BoundedFormula α m} (h : φ.IsAtomic)
  proof: IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

中文:
定理 是原子的.relabel
  结论: {m : 自然数} {φ : L.BoundedFormula α m} (h : φ.是原子的)
  证明: IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

Depends on / 依赖: IsAtomic, IsAtomic.equal, IsAtomic.recOn, IsAtomic.rel
-/
theorem IsAtomic.relabel {m : Nat} {φ : L.BoundedFormula α m} (h : φ.IsAtomic)
    (f : α -> β oplus (Fin n)) : (φ.relabel f).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

/--
theorem `IsAtomic.liftAt` / 定理 `IsAtomic.liftAt`

English:
theorem IsAtomic.liftAt
  given: {k m : Nat} (h : IsAtomic φ)
  statement: (φ.liftAt k m).IsAtomic
  proof: IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

中文:
定理 是原子的.liftAt
  条件: {k m : 自然数} (h : 是原子的 φ)
  结论: (φ.liftAt k m).是原子的
  证明: IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

Depends on / 依赖: IsAtomic, IsAtomic.equal, IsAtomic.recOn, IsAtomic.rel
-/
theorem IsAtomic.liftAt {k m : Nat} (h : IsAtomic φ) : (φ.liftAt k m).IsAtomic :=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

/--
theorem `IsAtomic.castLE` / 定理 `IsAtomic.castLE`

English:
theorem IsAtomic.castLE
  given: {h : l <= n} (hφ : IsAtomic φ)
  statement: (φ.castLE h).IsAtomic
  proof: IsAtomic.recOn hφ (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

中文:
定理 是原子的.castLE
  条件: {h : l <= n} (hφ : 是原子的 φ)
  结论: (φ.castLE h).是原子的
  证明: IsAtomic.recOn hφ (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

Depends on / 依赖: IsAtomic, IsAtomic.equal, IsAtomic.recOn, IsAtomic.rel
-/
theorem IsAtomic.castLE {h : l <= n} (hφ : IsAtomic φ) : (φ.castLE h).IsAtomic :=
  IsAtomic.recOn hφ (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _

/--
Inductive type `IsQF` / 归纳类型 `IsQF`

English:
inductive IsQF
  parameters: : L.BoundedFormula α n -> Prop
  constructors (3):
    - falsum: IsQF falsum
    - of_isAtomic: {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsQF φ
    - imp: {φ₁ φ₂ : L.BoundedFormula α n} (h₁ : IsQF φ₁) (h₂ : IsQF φ₂) : IsQF (φ₁.imp φ₂)

中文:
归纳类型 是QF
  参数: : L.BoundedFormula α n -> 命题
  构造子 (3 个):
    - falsum: 是QF falsum
    - of_isAtomic: {φ : L.BoundedFormula α n} (h : 是原子的 φ) : 是QF φ
    - imp: {φ₁ φ₂ : L.BoundedFormula α n} (h₁ : 是QF φ₁) (h₂ : 是QF φ₂) : 是QF (φ₁.imp φ₂)
-/
inductive IsQF : L.BoundedFormula α n -> Prop
  | falsum : IsQF falsum
  | of_isAtomic {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsQF φ
  | imp {φ₁ φ₂ : L.BoundedFormula α n} (h₁ : IsQF φ₁) (h₂ : IsQF φ₂) : IsQF (φ₁.imp φ₂)

/--
theorem `IsAtomic.isQF` / 定理 `IsAtomic.isQF`

English:
theorem IsAtomic.isQF
  given: {φ : L.BoundedFormula α n}
  statement: IsAtomic φ -> IsQF φ
  proof: IsQF.of_isAtomic

中文:
定理 是原子的.isQF
  条件: {φ : L.BoundedFormula α n}
  结论: 是原子的 φ -> 是QF φ
  证明: IsQF.of_isAtomic

Depends on / 依赖: IsQF.of_isAtomic, of_isAtomic
-/
theorem IsAtomic.isQF {φ : L.BoundedFormula α n} : IsAtomic φ -> IsQF φ :=
  IsQF.of_isAtomic

/--
theorem `isQF_bot` / 定理 `isQF_bot`

English:
theorem isQF_bot
  statement: IsQF (⊥ : L.BoundedFormula α n)
  proof: IsQF.falsum

中文:
定理 isQF_bot
  结论: 是QF (⊥ : L.BoundedFormula α n)
  证明: IsQF.falsum

Depends on / 依赖: IsQF.falsum, falsum
-/
theorem isQF_bot : IsQF (⊥ : L.BoundedFormula α n) :=
  IsQF.falsum

namespace IsQF

/--
theorem `not` / 定理 `not`

English:
theorem not
  given: {φ : L.BoundedFormula α n} (h : IsQF φ)
  statement: IsQF φ.not
  proof: h.imp isQF_bot

中文:
定理 not
  条件: {φ : L.BoundedFormula α n} (h : 是QF φ)
  结论: 是QF φ.not
  证明: h.imp isQF_bot

Depends on / 依赖: h.imp, isQF_bot
-/
theorem not {φ : L.BoundedFormula α n} (h : IsQF φ) : IsQF φ.not :=
  h.imp isQF_bot

/--
theorem `top` / 定理 `top`

English:
theorem top
  statement: IsQF (⊤ : L.BoundedFormula α n)
  proof: isQF_bot.not

中文:
定理 top
  结论: 是QF (⊤ : L.BoundedFormula α n)
  证明: isQF_bot.not

Depends on / 依赖: isQF_bot, isQF_bot.not
-/
theorem top : IsQF (⊤ : L.BoundedFormula α n) := isQF_bot.not

/--
theorem `sup` / 定理 `sup`

English:
theorem sup
  given: {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsQF ψ)
  statement: IsQF (φ ⊔ ψ)
  proof: hφ.not.imp hψ

中文:
定理 上确界
  条件: {φ ψ : L.BoundedFormula α n} (hφ : 是QF φ) (hψ : 是QF ψ)
  结论: 是QF (φ ⊔ ψ)
  证明: hφ.not.imp hψ

Depends on / 依赖: not.imp
-/
theorem sup {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsQF ψ) : IsQF (φ ⊔ ψ) :=
  hφ.not.imp hψ

/--
theorem `inf` / 定理 `inf`

English:
theorem inf
  given: {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsQF ψ)
  statement: IsQF (φ ⊓ ψ)
  proof: (hφ.imp hψ.not).not

中文:
定理 下确界
  条件: {φ ψ : L.BoundedFormula α n} (hφ : 是QF φ) (hψ : 是QF ψ)
  结论: 是QF (φ ⊓ ψ)
  证明: (hφ.imp hψ.not).not
-/
theorem inf {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsQF ψ) : IsQF (φ ⊓ ψ) :=
  (hφ.imp hψ.not).not

/--
theorem `relabel` / 定理 `relabel`

English:
theorem relabel
  given: {m : Nat} {φ : L.BoundedFormula α m} (h : φ.IsQF) (f : α -> β oplus (Fin n))
  proof: IsQF.recOn h isQF_bot (fun h => (h.relabel f).isQF) fun _ _ h1 h2 => h1.imp h2

中文:
定理 relabel
  条件: {m : 自然数} {φ : L.BoundedFormula α m} (h : φ.是QF) (f : α -> β oplus (有限集 n))
  证明: IsQF.recOn h isQF_bot (fun h => (h.relabel f).isQF) fun _ _ h1 h2 => h1.imp h2
-/
protected theorem relabel {m : Nat} {φ : L.BoundedFormula α m} (h : φ.IsQF) (f : α -> β oplus (Fin n)) :
    (φ.relabel f).IsQF :=
  IsQF.recOn h isQF_bot (fun h => (h.relabel f).isQF) fun _ _ h1 h2 => h1.imp h2

/--
theorem `liftAt` / 定理 `liftAt`

English:
theorem liftAt
  given: {k m : Nat} (h : IsQF φ)
  statement: (φ.liftAt k m).IsQF
  proof: IsQF.recOn h isQF_bot (fun ih => ih.liftAt.isQF) fun _ _ ih1 ih2 => ih1.imp ih2

中文:
定理 liftAt
  条件: {k m : 自然数} (h : 是QF φ)
  结论: (φ.liftAt k m).是QF
  证明: IsQF.recOn h isQF_bot (fun ih => ih.liftAt.isQF) fun _ _ ih1 ih2 => ih1.imp ih2
-/
protected theorem liftAt {k m : Nat} (h : IsQF φ) : (φ.liftAt k m).IsQF :=
  IsQF.recOn h isQF_bot (fun ih => ih.liftAt.isQF) fun _ _ ih1 ih2 => ih1.imp ih2

/--
theorem `castLE` / 定理 `castLE`

English:
theorem castLE
  given: {h : l <= n} (hφ : IsQF φ)
  statement: (φ.castLE h).IsQF
  proof: IsQF.recOn hφ isQF_bot (fun ih => ih.castLE.isQF) fun _ _ ih1 ih2 => ih1.imp ih2

中文:
定理 castLE
  条件: {h : l <= n} (hφ : 是QF φ)
  结论: (φ.castLE h).是QF
  证明: IsQF.recOn hφ isQF_bot (fun ih => ih.castLE.isQF) fun _ _ ih1 ih2 => ih1.imp ih2
-/
protected theorem castLE {h : l <= n} (hφ : IsQF φ) : (φ.castLE h).IsQF :=
  IsQF.recOn hφ isQF_bot (fun ih => ih.castLE.isQF) fun _ _ ih1 ih2 => ih1.imp ih2

end IsQF

/--
theorem `not_all_isQF` / 定理 `not_all_isQF`

English:
theorem not_all_isQF
  given: (φ : L.BoundedFormula α (n + 1))
  statement: ¬φ.all.IsQF
  proof: fun con => by
  obtain - | con := con
  exact φ.not_all_isAtomic con

中文:
定理 not_all_isQF
  条件: (φ : L.BoundedFormula α (n + 1))
  结论: ¬φ.all.是QF
  证明: fun con => by
  obtain - | con := con
  exact φ.not_all_isAtomic con

Depends on / 依赖: not_all_isAtomic
-/
theorem not_all_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.all.IsQF := fun con => by
  obtain - | con := con
  exact φ.not_all_isAtomic con

/--
theorem `not_ex_isQF` / 定理 `not_ex_isQF`

English:
theorem not_ex_isQF
  given: (φ : L.BoundedFormula α (n + 1))
  statement: ¬φ.ex.IsQF
  proof: fun con => by
  obtain - | con | con := con
  · exact φ.not_ex_isAtomic con
  · exact not_all_isQF _ con

中文:
定理 not_ex_isQF
  条件: (φ : L.BoundedFormula α (n + 1))
  结论: ¬φ.ex.是QF
  证明: fun con => by
  obtain - | con | con := con
  · exact φ.not_ex_isAtomic con
  · exact not_all_isQF _ con

Depends on / 依赖: not_all_isQF, not_ex_isAtomic
-/
theorem not_ex_isQF (φ : L.BoundedFormula α (n + 1)) : ¬φ.ex.IsQF := fun con => by
  obtain - | con | con := con
  · exact φ.not_ex_isAtomic con
  · exact not_all_isQF _ con

/--
Inductive type `IsPrenex` / 归纳类型 `IsPrenex`

English:
inductive IsPrenex
  parameters: : forall {n}, L.BoundedFormula α n -> Prop
  constructors (3):
    - of_isQF: {n : Nat} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsPrenex φ
    - all: {n : Nat} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.all
    - ex: {n : Nat} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.ex

中文:
归纳类型 是Prenex
  参数: : 对任意 {n}, L.BoundedFormula α n -> 命题
  构造子 (3 个):
    - of_isQF: {n : 自然数} {φ : L.BoundedFormula α n} (h : 是QF φ) : 是Prenex φ
    - all: {n : 自然数} {φ : L.BoundedFormula α (n + 1)} (h : 是Prenex φ) : 是Prenex φ.all
    - ex: {n : 自然数} {φ : L.BoundedFormula α (n + 1)} (h : 是Prenex φ) : 是Prenex φ.ex
-/
inductive IsPrenex : forall {n}, L.BoundedFormula α n -> Prop
  | of_isQF {n : Nat} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsPrenex φ
  | all {n : Nat} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.all
  | ex {n : Nat} {φ : L.BoundedFormula α (n + 1)} (h : IsPrenex φ) : IsPrenex φ.ex

/--
theorem `IsQF.isPrenex` / 定理 `IsQF.isPrenex`

English:
theorem IsQF.isPrenex
  given: {φ : L.BoundedFormula α n}
  statement: IsQF φ -> IsPrenex φ
  proof: IsPrenex.of_isQF

中文:
定理 是QF.isPrenex
  条件: {φ : L.BoundedFormula α n}
  结论: 是QF φ -> 是Prenex φ
  证明: IsPrenex.of_isQF

Depends on / 依赖: IsPrenex, IsPrenex.of_isQF, of_isQF
-/
theorem IsQF.isPrenex {φ : L.BoundedFormula α n} : IsQF φ -> IsPrenex φ :=
  IsPrenex.of_isQF

/--
theorem `IsAtomic.isPrenex` / 定理 `IsAtomic.isPrenex`

English:
theorem IsAtomic.isPrenex
  given: {φ : L.BoundedFormula α n} (h : IsAtomic φ)
  statement: IsPrenex φ
  proof: h.isQF.isPrenex

中文:
定理 是原子的.isPrenex
  条件: {φ : L.BoundedFormula α n} (h : 是原子的 φ)
  结论: 是Prenex φ
  证明: h.isQF.isPrenex

Depends on / 依赖: h.isQF.isPrenex, isPrenex
-/
theorem IsAtomic.isPrenex {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsPrenex φ :=
  h.isQF.isPrenex

/--
theorem `IsPrenex.induction_on_all_not` / 定理 `IsPrenex.induction_on_all_not`

English:
theorem IsPrenex.induction_on_all_not
  statement: {P : forall {n}, L.BoundedFormula α n -> Prop}
  proof: IsPrenex.recOn h hq (fun _ => ha) fun _ ih => hn (ha (hn ih))

中文:
定理 是Prenex.induction_on_all_not
  结论: {P : 对任意 {n}, L.BoundedFormula α n -> 命题}
  证明: IsPrenex.recOn h hq (fun _ => ha) fun _ ih => hn (ha (hn ih))

Depends on / 依赖: IsPrenex, IsPrenex.recOn
-/
theorem IsPrenex.induction_on_all_not {P : forall {n}, L.BoundedFormula α n -> Prop}
    {φ : L.BoundedFormula α n} (h : IsPrenex φ)
    (hq : forall {m} {ψ : L.BoundedFormula α m}, ψ.IsQF -> P ψ)
    (ha : forall {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ -> P ψ.all)
    (hn : forall {m} {ψ : L.BoundedFormula α m}, P ψ -> P ψ.not) : P φ :=
  IsPrenex.recOn h hq (fun _ => ha) fun _ ih => hn (ha (hn ih))

/--
theorem `IsPrenex.relabel` / 定理 `IsPrenex.relabel`

English:
theorem IsPrenex.relabel
  statement: {m : Nat} {φ : L.BoundedFormula α m} (h : φ.IsPrenex)
  proof: IsPrenex.recOn h (fun h => (h.relabel f).isPrenex) (fun _ h => by simp [h.all])
    fun _ h => by simp [h.ex]

中文:
定理 是Prenex.relabel
  结论: {m : 自然数} {φ : L.BoundedFormula α m} (h : φ.是Prenex)
  证明: IsPrenex.recOn h (fun h => (h.relabel f).isPrenex) (fun _ h => by simp [h.all])
    fun _ h => by simp [h.ex]

Depends on / 依赖: IsPrenex, IsPrenex.recOn, h.all, h.ex, h.relabel, isPrenex, relabel
-/
theorem IsPrenex.relabel {m : Nat} {φ : L.BoundedFormula α m} (h : φ.IsPrenex)
    (f : α -> β oplus (Fin n)) : (φ.relabel f).IsPrenex :=
  IsPrenex.recOn h (fun h => (h.relabel f).isPrenex) (fun _ h => by simp [h.all])
    fun _ h => by simp [h.ex]

/--
theorem `IsPrenex.castLE` / 定理 `IsPrenex.castLE`

English:
theorem IsPrenex.castLE
  given: (hφ : IsPrenex φ)
  statement: forall {n} {h : l <= n}, (φ.castLE h).IsPrenex
  proof: IsPrenex.recOn (motive := @fun l φ _ => forall (n : Nat) (h : l <= n), (φ.castLE h).IsPrenex) hφ
    (@fun _ _ ih _ _ => ih.castLE.isPrenex)
    (@fun _ _ _ ih _ _ => (ih _ _).all)
    (@fun _ _ _ ih _ _ => (ih _ _).ex) _ _

中文:
定理 是Prenex.castLE
  条件: (hφ : 是Prenex φ)
  结论: 对任意 {n} {h : l <= n}, (φ.castLE h).是Prenex
  证明: IsPrenex.recOn (motive := @fun l φ _ => forall (n : Nat) (h : l <= n), (φ.castLE h).IsPrenex) hφ
    (@fun _ _ ih _ _ => ih.castLE.isPrenex)
    (@fun _ _ _ ih _ _ => (ih _ _).all)
    (@fun _ _ _ ih _ _ => (ih _ _).ex) _ _

Depends on / 依赖: IsPrenex, IsPrenex.recOn, castLE, ih.castLE.isPrenex, isPrenex, motive
-/
theorem IsPrenex.castLE (hφ : IsPrenex φ) : forall {n} {h : l <= n}, (φ.castLE h).IsPrenex :=
  IsPrenex.recOn (motive := @fun l φ _ => forall (n : Nat) (h : l <= n), (φ.castLE h).IsPrenex) hφ
    (@fun _ _ ih _ _ => ih.castLE.isPrenex)
    (@fun _ _ _ ih _ _ => (ih _ _).all)
    (@fun _ _ _ ih _ _ => (ih _ _).ex) _ _

/--
theorem `IsPrenex.liftAt` / 定理 `IsPrenex.liftAt`

English:
theorem IsPrenex.liftAt
  given: {k m : Nat} (h : IsPrenex φ)
  statement: (φ.liftAt k m).IsPrenex
  proof: IsPrenex.recOn h (fun ih => ih.liftAt.isPrenex) (fun _ ih => ih.castLE.all)
    fun _ ih => ih.castLE.ex

中文:
定理 是Prenex.liftAt
  条件: {k m : 自然数} (h : 是Prenex φ)
  结论: (φ.liftAt k m).是Prenex
  证明: IsPrenex.recOn h (fun ih => ih.liftAt.isPrenex) (fun _ ih => ih.castLE.all)
    fun _ ih => ih.castLE.ex

Depends on / 依赖: IsPrenex, IsPrenex.recOn, castLE, ih.castLE.all, ih.castLE.ex, ih.liftAt.isPrenex, isPrenex, liftAt
-/
theorem IsPrenex.liftAt {k m : Nat} (h : IsPrenex φ) : (φ.liftAt k m).IsPrenex :=
  IsPrenex.recOn h (fun ih => ih.liftAt.isPrenex) (fun _ ih => ih.castLE.all)
    fun _ ih => ih.castLE.ex

/--
Definition of `toPrenexImpRight` / `toPrenexImpRight` 的定义

English:
definition toPrenexImpRight
  signature: : forall {n}, L.BoundedFormula α n -> L.BoundedFormula α n -> L.BoundedFormula α n

中文:
定义 toPrenexImpRight
  签名: : 对任意 {n}, L.BoundedFormula α n -> L.BoundedFormula α n -> L.BoundedFormula α n
-/
def toPrenexImpRight : forall {n}, L.BoundedFormula α n -> L.BoundedFormula α n -> L.BoundedFormula α n
  | n, φ, BoundedFormula.ex ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).ex
  | n, φ, all ψ => ((φ.liftAt 1 n).toPrenexImpRight ψ).all
  | _n, φ, ψ => φ.imp ψ

/--
theorem `IsQF.toPrenexImpRight` / 定理 `IsQF.toPrenexImpRight`

English:
theorem IsQF.toPrenexImpRight
  given: {φ : L.BoundedFormula α n}

中文:
定理 是QF.toPrenexImpRight
  条件: {φ : L.BoundedFormula α n}
-/
theorem IsQF.toPrenexImpRight {φ : L.BoundedFormula α n} :
    forall {ψ : L.BoundedFormula α n}, IsQF ψ -> φ.toPrenexImpRight ψ = φ.imp ψ
  | _, IsQF.falsum => rfl
  | _, IsQF.of_isAtomic (IsAtomic.equal _ _) => rfl
  | _, IsQF.of_isAtomic (IsAtomic.rel _ _) => rfl
  | _, IsQF.imp IsQF.falsum _ => rfl
  | _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.equal _ _)) _ => rfl
  | _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.rel _ _)) _ => rfl
  | _, IsQF.imp (IsQF.imp _ _) _ => rfl

/--
theorem `isPrenex_toPrenexImpRight` / 定理 `isPrenex_toPrenexImpRight`

English:
theorem isPrenex_toPrenexImpRight
  given: {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ)
  proof: by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]; exact (hφ.imp hψ).isPrenex
  | all _ ih1 => exact (ih1 hφ.liftAt).all
  | ex _ ih2 => exact (ih2 hφ.liftAt).ex

中文:
定理 isPrenex_toPrenexImpRight
  条件: {φ ψ : L.BoundedFormula α n} (hφ : 是QF φ) (hψ : 是Prenex ψ)
  证明: by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]; exact (hφ.imp hψ).isPrenex
  | all _ ih1 => exact (ih1 hφ.liftAt).all
  | ex _ ih2 => exact (ih2 hφ.liftAt).ex

Depends on / 依赖: isPrenex, liftAt, of_isQF, toPrenexImpRight
-/
theorem isPrenex_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImpRight ψ) := by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]; exact (hφ.imp hψ).isPrenex
  | all _ ih1 => exact (ih1 hφ.liftAt).all
  | ex _ ih2 => exact (ih2 hφ.liftAt).ex

/--
Definition of `toPrenexImp` / `toPrenexImp` 的定义

English:
definition toPrenexImp
  signature: : forall {n}, L.BoundedFormula α n -> L.BoundedFormula α n -> L.BoundedFormula α n

中文:
定义 toPrenexImp
  签名: : 对任意 {n}, L.BoundedFormula α n -> L.BoundedFormula α n -> L.BoundedFormula α n
-/
def toPrenexImp : forall {n}, L.BoundedFormula α n -> L.BoundedFormula α n -> L.BoundedFormula α n
  | n, BoundedFormula.ex φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).all
  | n, all φ, ψ => (φ.toPrenexImp (ψ.liftAt 1 n)).ex
  | _, φ, ψ => φ.toPrenexImpRight ψ

/--
theorem `IsQF.toPrenexImp` / 定理 `IsQF.toPrenexImp`

English:
theorem IsQF.toPrenexImp

中文:
定理 是QF.toPrenexImp
-/
theorem IsQF.toPrenexImp :
    forall {φ ψ : L.BoundedFormula α n}, φ.IsQF -> φ.toPrenexImp ψ = φ.toPrenexImpRight ψ
  | _, _, IsQF.falsum => rfl
  | _, _, IsQF.of_isAtomic (IsAtomic.equal _ _) => rfl
  | _, _, IsQF.of_isAtomic (IsAtomic.rel _ _) => rfl
  | _, _, IsQF.imp IsQF.falsum _ => rfl
  | _, _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.equal _ _)) _ => rfl
  | _, _, IsQF.imp (IsQF.of_isAtomic (IsAtomic.rel _ _)) _ => rfl
  | _, _, IsQF.imp (IsQF.imp _ _) _ => rfl

/--
theorem `isPrenex_toPrenexImp` / 定理 `isPrenex_toPrenexImp`

English:
theorem isPrenex_toPrenexImp
  given: {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ)
  proof: by
  induction hφ with
  | of_isQF hφ => rw [hφ.toPrenexImp]; exact isPrenex_toPrenexImpRight hφ hψ
  | all _ ih1 => exact (ih1 hψ.liftAt).ex
  | ex _ ih2 => exact (ih2 hψ.liftAt).all

中文:
定理 isPrenex_toPrenexImp
  条件: {φ ψ : L.BoundedFormula α n} (hφ : 是Prenex φ) (hψ : 是Prenex ψ)
  证明: by
  induction hφ with
  | of_isQF hφ => rw [hφ.toPrenexImp]; exact isPrenex_toPrenexImpRight hφ hψ
  | all _ ih1 => exact (ih1 hψ.liftAt).ex
  | ex _ ih2 => exact (ih2 hψ.liftAt).all

Depends on / 依赖: isPrenex_toPrenexImpRight, liftAt, of_isQF, toPrenexImp
-/
theorem isPrenex_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ) :
    IsPrenex (φ.toPrenexImp ψ) := by
  induction hφ with
  | of_isQF hφ => rw [hφ.toPrenexImp]; exact isPrenex_toPrenexImpRight hφ hψ
  | all _ ih1 => exact (ih1 hψ.liftAt).ex
  | ex _ ih2 => exact (ih2 hψ.liftAt).all

/--
Definition of `toPrenex` / `toPrenex` 的定义

English:
definition toPrenex
  signature: : forall {n}, L.BoundedFormula α n -> L.BoundedFormula α n

中文:
定义 toPrenex
  签名: : 对任意 {n}, L.BoundedFormula α n -> L.BoundedFormula α n
-/
def toPrenex : forall {n}, L.BoundedFormula α n -> L.BoundedFormula α n
  | _, falsum => ⊥
  | _, equal t₁ t₂ => t₁.bdEqual t₂
  | _, rel R ts => rel R ts
  | _, imp f₁ f₂ => f₁.toPrenex.toPrenexImp f₂.toPrenex
  | _, all f => f.toPrenex.all

/--
theorem `toPrenex_isPrenex` / 定理 `toPrenex_isPrenex`

English:
theorem toPrenex_isPrenex
  given: (φ : L.BoundedFormula α n)
  statement: φ.toPrenex.IsPrenex
  proof: BoundedFormula.recOn φ isQF_bot.isPrenex (fun _ _ => (IsAtomic.equal _ _).isPrenex)
    (fun _ _ => (IsAtomic.rel _ _).isPrenex) (fun _ _ h1 h2 => isPrenex_toPrenexImp h1 h2)
    fun _ => IsPrenex.all

中文:
定理 toPrenex_isPrenex
  条件: (φ : L.BoundedFormula α n)
  结论: φ.toPrenex.是Prenex
  证明: BoundedFormula.recOn φ isQF_bot.isPrenex (fun _ _ => (IsAtomic.equal _ _).isPrenex)
    (fun _ _ => (IsAtomic.rel _ _).isPrenex) (fun _ _ h1 h2 => isPrenex_toPrenexImp h1 h2)
    fun _ => IsPrenex.all

Depends on / 依赖: BoundedFormula, BoundedFormula.recOn, IsAtomic, IsAtomic.equal, IsAtomic.rel, IsPrenex, IsPrenex.all, isPrenex, isPrenex_toPrenexImp, isQF_bot, isQF_bot.isPrenex
-/
theorem toPrenex_isPrenex (φ : L.BoundedFormula α n) : φ.toPrenex.IsPrenex :=
  BoundedFormula.recOn φ isQF_bot.isPrenex (fun _ _ => (IsAtomic.equal _ _).isPrenex)
    (fun _ _ => (IsAtomic.rel _ _).isPrenex) (fun _ _ h1 h2 => isPrenex_toPrenexImp h1 h2)
    fun _ => IsPrenex.all

variable [Nonempty M]

/--
theorem `realize_toPrenexImpRight` / 定理 `realize_toPrenexImpRight`

English:
theorem realize_toPrenexImpRight
  statement: {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ)
  proof: by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]
  | all _ ih =>
    refine _root_.trans (forall_congr' fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact ⟨fun h1 a h2 => h1 h2 a, fun h1 h2 a => h1 a h2⟩
  | ex _ ih =>
    unfold toPrenexImpRight
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_ex]
    refine ⟨?_, fun h' => ?_⟩
    · rintro ⟨a, ha⟩ h
      exact ⟨a, ha h⟩
    · by_cases h : φ.Realize v xs
      · obtain ⟨a, ha⟩ := h' h
        exact ⟨a, fun _ => ha⟩
      · inhabit M
        exact ⟨default, fun h'' => (h h'').elim⟩

中文:
定理 realize_toPrenexImpRight
  结论: {φ ψ : L.BoundedFormula α n} (hφ : 是QF φ) (hψ : 是Prenex ψ)
  证明: by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]
  | all _ ih =>
    refine _root_.trans (forall_congr' fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact ⟨fun h1 a h2 => h1 h2 a, fun h1 h2 a => h1 a h2⟩
  | ex _ ih =>
    unfold toPrenexImpRight
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_ex]
    refine ⟨?_, fun h' => ?_⟩
    · rintro ⟨a, ha⟩ h
      exact ⟨a, ha h⟩
    · by_cases h : φ.Realize v xs
      · obtain ⟨a, ha⟩ := h' h
        exact ⟨a, fun _ => ha⟩
      · inhabit M
        exact ⟨default, fun h'' => (h h'').elim⟩

Depends on / 依赖: _root_, _root_.trans, exists_congr, forall_congr, liftAt, of_isQF, realize_all, realize_ex, realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, toPrenexImpRight
-/
theorem realize_toPrenexImpRight {φ ψ : L.BoundedFormula α n} (hφ : IsQF φ) (hψ : IsPrenex ψ)
    {v : α -> M} {xs : Fin n -> M} :
    (φ.toPrenexImpRight ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  induction hψ with
  | of_isQF hψ => rw [hψ.toPrenexImpRight]
  | all _ ih =>
    refine _root_.trans (forall_congr' fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact ⟨fun h1 a h2 => h1 h2 a, fun h1 h2 a => h1 a h2⟩
  | ex _ ih =>
    unfold toPrenexImpRight
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hφ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_ex]
    refine ⟨?_, fun h' => ?_⟩
    · rintro ⟨a, ha⟩ h
      exact ⟨a, ha h⟩
    · by_cases h : φ.Realize v xs
      · obtain ⟨a, ha⟩ := h' h
        exact ⟨a, fun _ => ha⟩
      · inhabit M
        exact ⟨default, fun h'' => (h h'').elim⟩

/--
theorem `realize_toPrenexImp` / 定理 `realize_toPrenexImp`

English:
theorem realize_toPrenexImp
  statement: {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ)
  proof: by
  revert ψ
  induction hφ with
  | of_isQF hφ =>
    intro ψ hψ
    rw [hφ.toPrenexImp]
    exact realize_toPrenexImpRight hφ hψ
  | all _ ih =>
    intro ψ hψ
    unfold toPrenexImp
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hψ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact Iff.symm forall_imp_iff_exists_imp
  | ex _ ih =>
    intro ψ hψ
    refine _root_.trans (forall_congr' fun _ => ih hψ.liftAt) ?_
    simp

@[simp]

中文:
定理 realize_toPrenexImp
  结论: {φ ψ : L.BoundedFormula α n} (hφ : 是Prenex φ) (hψ : 是Prenex ψ)
  证明: by
  revert ψ
  induction hφ with
  | of_isQF hφ =>
    intro ψ hψ
    rw [hφ.toPrenexImp]
    exact realize_toPrenexImpRight hφ hψ
  | all _ ih =>
    intro ψ hψ
    unfold toPrenexImp
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hψ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact Iff.symm forall_imp_iff_exists_imp
  | ex _ ih =>
    intro ψ hψ
    refine _root_.trans (forall_congr' fun _ => ih hψ.liftAt) ?_
    simp

@[simp]

Depends on / 依赖: Iff.symm, _root_, _root_.trans, exists_congr, forall_congr, forall_imp_iff_exists_imp, liftAt, of_isQF, realize_all, realize_ex, realize_imp, realize_liftAt_one_self, realize_toPrenexImpRight, revert, snoc_comp_castSucc, toPrenexImp
-/
theorem realize_toPrenexImp {φ ψ : L.BoundedFormula α n} (hφ : IsPrenex φ) (hψ : IsPrenex ψ)
    {v : α -> M} {xs : Fin n -> M} : (φ.toPrenexImp ψ).Realize v xs ↔ (φ.imp ψ).Realize v xs := by
  revert ψ
  induction hφ with
  | of_isQF hφ =>
    intro ψ hψ
    rw [hφ.toPrenexImp]
    exact realize_toPrenexImpRight hφ hψ
  | all _ ih =>
    intro ψ hψ
    unfold toPrenexImp
    rw [realize_ex]
    refine _root_.trans (exists_congr fun _ => ih hψ.liftAt) ?_
    simp only [realize_imp, realize_liftAt_one_self, snoc_comp_castSucc, realize_all]
    exact Iff.symm forall_imp_iff_exists_imp
  | ex _ ih =>
    intro ψ hψ
    refine _root_.trans (forall_congr' fun _ => ih hψ.liftAt) ?_
    simp

@[simp]
/--
theorem `realize_toPrenex` / 定理 `realize_toPrenex`

English:
theorem realize_toPrenex
  given: (φ : L.BoundedFormula α n) {v : α -> M}
  proof: by
  induction φ with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp f1 f2 h1 h2 =>
    intros
    rw [toPrenex]; rw [realize_toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex]; rw [realize_imp]; rw [realize_imp]; rw [h1]; rw [h2]
  | all _ h =>
    intros
    rw [realize_all]; rw [toPrenex]; rw [realize_all]
    exact forall_congr' fun a => h

中文:
定理 realize_toPrenex
  条件: (φ : L.BoundedFormula α n) {v : α -> M}
  证明: by
  induction φ with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp f1 f2 h1 h2 =>
    intros
    rw [toPrenex]; rw [realize_toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex]; rw [realize_imp]; rw [realize_imp]; rw [h1]; rw [h2]
  | all _ h =>
    intros
    rw [realize_all]; rw [toPrenex]; rw [realize_all]
    exact forall_congr' fun a => h

Depends on / 依赖: Iff.rfl, f1.toPrenex_isPrenex, f2.toPrenex_isPrenex, falsum, forall_congr, intros, realize_all, realize_imp, realize_toPrenexImp, toPrenex, toPrenex_isPrenex
-/
theorem realize_toPrenex (φ : L.BoundedFormula α n) {v : α -> M} :
    forall {xs : Fin n -> M}, φ.toPrenex.Realize v xs ↔ φ.Realize v xs := by
  induction φ with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp f1 f2 h1 h2 =>
    intros
    rw [toPrenex]; rw [realize_toPrenexImp f1.toPrenex_isPrenex f2.toPrenex_isPrenex]; rw [realize_imp]; rw [realize_imp]; rw [h1]; rw [h2]
  | all _ h =>
    intros
    rw [realize_all]; rw [toPrenex]; rw [realize_all]
    exact forall_congr' fun a => h

/--
theorem `IsQF.induction_on_sup_not` / 定理 `IsQF.induction_on_sup_not`

English:
theorem IsQF.induction_on_sup_not
  statement: {P : L.BoundedFormula α n -> Prop} {φ : L.BoundedFormula α n}
  proof: IsQF.recOn h hf @ha fun {φ₁ φ₂} _ _ h1 h2 =>
    (hse (φ₁.imp_iff_not_sup φ₂)).2 (hsup (hnot h1) h2)

中文:
定理 是QF.induction_on_sup_not
  结论: {P : L.BoundedFormula α n -> 命题} {φ : L.BoundedFormula α n}
  证明: IsQF.recOn h hf @ha fun {φ₁ φ₂} _ _ h1 h2 =>
    (hse (φ₁.imp_iff_not_sup φ₂)).2 (hsup (hnot h1) h2)

Depends on / 依赖: IsQF.recOn, imp_iff_not_sup
-/
theorem IsQF.induction_on_sup_not {P : L.BoundedFormula α n -> Prop} {φ : L.BoundedFormula α n}
    (h : IsQF φ) (hf : P (⊥ : L.BoundedFormula α n))
    (ha : forall ψ : L.BoundedFormula α n, IsAtomic ψ -> P ψ)
    (hsup : forall {φ₁ φ₂}, P φ₁ -> P φ₂ -> P (φ₁ ⊔ φ₂)) (hnot : forall {φ}, P φ -> P φ.not)
    (hse :
      forall {φ₁ φ₂ : L.BoundedFormula α n}, (φ₁ ⇔[∅] φ₂) -> (P φ₁ ↔ P φ₂)) :
    P φ :=
  IsQF.recOn h hf @ha fun {φ₁ φ₂} _ _ h1 h2 =>
    (hse (φ₁.imp_iff_not_sup φ₂)).2 (hsup (hnot h1) h2)

/--
theorem `IsQF.induction_on_inf_not` / 定理 `IsQF.induction_on_inf_not`

English:
theorem IsQF.induction_on_inf_not
  statement: {P : L.BoundedFormula α n -> Prop} {φ : L.BoundedFormula α n}
  proof: h.induction_on_sup_not hf ha
    (fun {φ₁ φ₂} h1 h2 =>
      (hse (φ₁.sup_iff_not_inf_not φ₂)).2 (hnot (hinf (hnot h1) (hnot h2))))
    (fun {_} => hnot) fun {_ _} => hse

中文:
定理 是QF.induction_on_inf_not
  结论: {P : L.BoundedFormula α n -> 命题} {φ : L.BoundedFormula α n}
  证明: h.induction_on_sup_not hf ha
    (fun {φ₁ φ₂} h1 h2 =>
      (hse (φ₁.sup_iff_not_inf_not φ₂)).2 (hnot (hinf (hnot h1) (hnot h2))))
    (fun {_} => hnot) fun {_ _} => hse

Depends on / 依赖: h.induction_on_sup_not, induction_on_sup_not, sup_iff_not_inf_not
-/
theorem IsQF.induction_on_inf_not {P : L.BoundedFormula α n -> Prop} {φ : L.BoundedFormula α n}
    (h : IsQF φ) (hf : P (⊥ : L.BoundedFormula α n))
    (ha : forall ψ : L.BoundedFormula α n, IsAtomic ψ -> P ψ)
    (hinf : forall {φ₁ φ₂}, P φ₁ -> P φ₂ -> P (φ₁ ⊓ φ₂)) (hnot : forall {φ}, P φ -> P φ.not)
    (hse :
      forall {φ₁ φ₂ : L.BoundedFormula α n}, (φ₁ ⇔[∅] φ₂) -> (P φ₁ ↔ P φ₂)) :
    P φ :=
  h.induction_on_sup_not hf ha
    (fun {φ₁ φ₂} h1 h2 =>
      (hse (φ₁.sup_iff_not_inf_not φ₂)).2 (hnot (hinf (hnot h1) (hnot h2))))
    (fun {_} => hnot) fun {_ _} => hse

/--
theorem `iff_toPrenex` / 定理 `iff_toPrenex`

English:
theorem iff_toPrenex
  given: (φ : L.BoundedFormula α n)
  proof: fun M v xs => by
  rw [realize_iff]; rw [realize_toPrenex]

中文:
定理 iff_toPrenex
  条件: (φ : L.BoundedFormula α n)
  证明: fun M v xs => by
  rw [realize_iff]; rw [realize_toPrenex]

Depends on / 依赖: realize_iff, realize_toPrenex
-/
theorem iff_toPrenex (φ : L.BoundedFormula α n) :
    φ ⇔[∅] φ.toPrenex := fun M v xs => by
  rw [realize_iff]; rw [realize_toPrenex]

/--
theorem `induction_on_all_ex` / 定理 `induction_on_all_ex`

English:
theorem induction_on_all_ex
  statement: {P : forall {m}, L.BoundedFormula α m -> Prop} (φ : L.BoundedFormula α n)
  proof: by
  suffices h' : forall {m} {φ : L.BoundedFormula α m}, φ.IsPrenex -> P φ from
    (hse φ.iff_toPrenex).2 (h' φ.toPrenex_isPrenex)
  intro m φ hφ
  induction hφ with
  | of_isQF hφ => exact hqf hφ
  | all _ hφ => exact hall hφ
  | ex _ hφ => exact hex hφ

中文:
定理 induction_on_all_ex
  结论: {P : 对任意 {m}, L.BoundedFormula α m -> 命题} (φ : L.BoundedFormula α n)
  证明: by
  suffices h' : forall {m} {φ : L.BoundedFormula α m}, φ.IsPrenex -> P φ from
    (hse φ.iff_toPrenex).2 (h' φ.toPrenex_isPrenex)
  intro m φ hφ
  induction hφ with
  | of_isQF hφ => exact hqf hφ
  | all _ hφ => exact hall hφ
  | ex _ hφ => exact hex hφ

Depends on / 依赖: BoundedFormula, IsPrenex, L.BoundedFormula, iff_toPrenex, of_isQF, toPrenex_isPrenex
-/
theorem induction_on_all_ex {P : forall {m}, L.BoundedFormula α m -> Prop} (φ : L.BoundedFormula α n)
    (hqf : forall {m} {ψ : L.BoundedFormula α m}, IsQF ψ -> P ψ)
    (hall : forall {m} {ψ : L.BoundedFormula α (m + 1)}, P ψ -> P ψ.all)
    (hex : forall {m} {φ : L.BoundedFormula α (m + 1)}, P φ -> P φ.ex)
    (hse : forall {m} {φ₁ φ₂ : L.BoundedFormula α m},
      (φ₁ ⇔[∅] φ₂) -> (P φ₁ ↔ P φ₂)) :
    P φ := by
  suffices h' : forall {m} {φ : L.BoundedFormula α m}, φ.IsPrenex -> P φ from
    (hse φ.iff_toPrenex).2 (h' φ.toPrenex_isPrenex)
  intro m φ hφ
  induction hφ with
  | of_isQF hφ => exact hqf hφ
  | all _ hφ => exact hall hφ
  | ex _ hφ => exact hex hφ

/--
theorem `induction_on_exists_not` / 定理 `induction_on_exists_not`

English:
theorem induction_on_exists_not
  statement: {P : forall {m}, L.BoundedFormula α m -> Prop} (φ : L.BoundedFormula α n)
  proof: φ.induction_on_all_ex (fun {_ _} => hqf)
    (fun {_ φ} hφ => (hse φ.all_iff_not_ex_not).2 (hnot (hex (hnot hφ))))
    (fun {_ _} => hex) fun {_ _ _} => hse

中文:
定理 induction_on_存在_not
  结论: {P : 对任意 {m}, L.BoundedFormula α m -> 命题} (φ : L.BoundedFormula α n)
  证明: φ.induction_on_all_ex (fun {_ _} => hqf)
    (fun {_ φ} hφ => (hse φ.all_iff_not_ex_not).2 (hnot (hex (hnot hφ))))
    (fun {_ _} => hex) fun {_ _ _} => hse

Depends on / 依赖: all_iff_not_ex_not, induction_on_all_ex
-/
theorem induction_on_exists_not {P : forall {m}, L.BoundedFormula α m -> Prop} (φ : L.BoundedFormula α n)
    (hqf : forall {m} {ψ : L.BoundedFormula α m}, IsQF ψ -> P ψ)
    (hnot : forall {m} {φ : L.BoundedFormula α m}, P φ -> P φ.not)
    (hex : forall {m} {φ : L.BoundedFormula α (m + 1)}, P φ -> P φ.ex)
    (hse : forall {m} {φ₁ φ₂ : L.BoundedFormula α m},
      (φ₁ ⇔[∅] φ₂) -> (P φ₁ ↔ P φ₂)) :
    P φ :=
  φ.induction_on_all_ex (fun {_ _} => hqf)
    (fun {_ φ} hφ => (hse φ.all_iff_not_ex_not).2 (hnot (hex (hnot hφ))))
    (fun {_ _} => hex) fun {_ _ _} => hse

/--
Inductive type `IsUniversal` / 归纳类型 `IsUniversal`

English:
inductive IsUniversal
  parameters: : forall {n}, L.BoundedFormula α n -> Prop
  constructors (2):
    - of_isQF: {n : Nat} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsUniversal φ
    - all: {n : Nat} {φ : L.BoundedFormula α (n + 1)} (h : IsUniversal φ) : IsUniversal φ.all

中文:
归纳类型 是泛
  参数: : 对任意 {n}, L.BoundedFormula α n -> 命题
  构造子 (2 个):
    - of_isQF: {n : 自然数} {φ : L.BoundedFormula α n} (h : 是QF φ) : 是泛 φ
    - all: {n : 自然数} {φ : L.BoundedFormula α (n + 1)} (h : 是泛 φ) : 是泛 φ.all
-/
inductive IsUniversal : forall {n}, L.BoundedFormula α n -> Prop
  | of_isQF {n : Nat} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsUniversal φ
  | all {n : Nat} {φ : L.BoundedFormula α (n + 1)} (h : IsUniversal φ) : IsUniversal φ.all

/--
lemma `IsQF.isUniversal` / 引理 `IsQF.isUniversal`

English:
lemma IsQF.isUniversal
  given: {φ : L.BoundedFormula α n}
  statement: IsQF φ -> IsUniversal φ
  proof: IsUniversal.of_isQF

中文:
引理 是QF.isUniversal
  条件: {φ : L.BoundedFormula α n}
  结论: 是QF φ -> 是泛 φ
  证明: IsUniversal.of_isQF

Depends on / 依赖: IsUniversal, IsUniversal.of_isQF, of_isQF
-/
lemma IsQF.isUniversal {φ : L.BoundedFormula α n} : IsQF φ -> IsUniversal φ :=
  IsUniversal.of_isQF

/--
lemma `IsAtomic.isUniversal` / 引理 `IsAtomic.isUniversal`

English:
lemma IsAtomic.isUniversal
  given: {φ : L.BoundedFormula α n} (h : IsAtomic φ)
  statement: IsUniversal φ
  proof: h.isQF.isUniversal

中文:
引理 是原子的.isUniversal
  条件: {φ : L.BoundedFormula α n} (h : 是原子的 φ)
  结论: 是泛 φ
  证明: h.isQF.isUniversal

Depends on / 依赖: h.isQF.isUniversal, isUniversal
-/
lemma IsAtomic.isUniversal {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsUniversal φ :=
  h.isQF.isUniversal

/--
Inductive type `IsExistential` / 归纳类型 `IsExistential`

English:
inductive IsExistential
  parameters: : forall {n}, L.BoundedFormula α n -> Prop
  constructors (2):
    - of_isQF: {n : Nat} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsExistential φ
    - ex: {n : Nat} {φ : L.BoundedFormula α (n + 1)} (h : IsExistential φ) : IsExistential φ.ex

中文:
归纳类型 是存在
  参数: : 对任意 {n}, L.BoundedFormula α n -> 命题
  构造子 (2 个):
    - of_isQF: {n : 自然数} {φ : L.BoundedFormula α n} (h : 是QF φ) : 是存在 φ
    - ex: {n : 自然数} {φ : L.BoundedFormula α (n + 1)} (h : 是存在 φ) : 是存在 φ.ex
-/
inductive IsExistential : forall {n}, L.BoundedFormula α n -> Prop
  | of_isQF {n : Nat} {φ : L.BoundedFormula α n} (h : IsQF φ) : IsExistential φ
  | ex {n : Nat} {φ : L.BoundedFormula α (n + 1)} (h : IsExistential φ) : IsExistential φ.ex

/--
lemma `IsQF.isExistential` / 引理 `IsQF.isExistential`

English:
lemma IsQF.isExistential
  given: {φ : L.BoundedFormula α n}
  statement: IsQF φ -> IsExistential φ
  proof: IsExistential.of_isQF

中文:
引理 是QF.isExistential
  条件: {φ : L.BoundedFormula α n}
  结论: 是QF φ -> 是存在 φ
  证明: IsExistential.of_isQF

Depends on / 依赖: IsExistential, IsExistential.of_isQF, of_isQF
-/
lemma IsQF.isExistential {φ : L.BoundedFormula α n} : IsQF φ -> IsExistential φ :=
  IsExistential.of_isQF

/--
lemma `IsAtomic.isExistential` / 引理 `IsAtomic.isExistential`

English:
lemma IsAtomic.isExistential
  given: {φ : L.BoundedFormula α n} (h : IsAtomic φ)
  statement: IsExistential φ
  proof: h.isQF.isExistential

中文:
引理 是原子的.isExistential
  条件: {φ : L.BoundedFormula α n} (h : 是原子的 φ)
  结论: 是存在 φ
  证明: h.isQF.isExistential

Depends on / 依赖: h.isQF.isExistential, isExistential
-/
lemma IsAtomic.isExistential {φ : L.BoundedFormula α n} (h : IsAtomic φ) : IsExistential φ :=
  h.isQF.isExistential

section Preservation

variable {M : Type*} [L.Structure M] {N : Type*} [L.Structure N]
variable {F : Type*} [FunLike F M N]

/--
lemma `IsAtomic.realize_comp_of_injective` / 引理 `IsAtomic.realize_comp_of_injective`

English:
lemma IsAtomic.realize_comp_of_injective
  statement: {φ : L.BoundedFormula α n} (hA : φ.IsAtomic)
  proof: by
  induction hA with
  | equal t₁ t₂ => simp only [realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term, hInj.eq_iff,
    imp_self]
  | rel R ts =>
    simp only [realize_rel, ← Sum.comp_elim, HomClass.realize_term]
    exact HomClass.map_rel f R (fun i => Term.realize (Sum.elim v xs) (ts i))

中文:
引理 是原子的.realize_comp_of_injective
  结论: {φ : L.BoundedFormula α n} (hA : φ.是原子的)
  证明: by
  induction hA with
  | equal t₁ t₂ => simp only [realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term, hInj.eq_iff,
    imp_self]
  | rel R ts =>
    simp only [realize_rel, ← Sum.comp_elim, HomClass.realize_term]
    exact HomClass.map_rel f R (fun i => Term.realize (Sum.elim v xs) (ts i))

Depends on / 依赖: HomClass, HomClass.map_rel, HomClass.realize_term, Sum.comp_elim, Sum.elim, Term.realize, comp_elim, eq_iff, hInj.eq_iff, imp_self, map_rel, realize, realize_bdEqual, realize_rel, realize_term
-/
lemma IsAtomic.realize_comp_of_injective {φ : L.BoundedFormula α n} (hA : φ.IsAtomic)
    [L.HomClass F M N] {f : F} (hInj : Function.Injective f) {v : α -> M} {xs : Fin n -> M} :
    φ.Realize v xs -> φ.Realize (f ∘ v) (f ∘ xs) := by
  induction hA with
  | equal t₁ t₂ => simp only [realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term, hInj.eq_iff,
    imp_self]
  | rel R ts =>
    simp only [realize_rel, ← Sum.comp_elim, HomClass.realize_term]
    exact HomClass.map_rel f R (fun i => Term.realize (Sum.elim v xs) (ts i))

/--
lemma `IsAtomic.realize_comp` / 引理 `IsAtomic.realize_comp`

English:
lemma IsAtomic.realize_comp
  statement: {φ : L.BoundedFormula α n} (hA : φ.IsAtomic)
  proof: hA.realize_comp_of_injective (EmbeddingLike.injective f)

中文:
引理 是原子的.realize_comp
  结论: {φ : L.BoundedFormula α n} (hA : φ.是原子的)
  证明: hA.realize_comp_of_injective (EmbeddingLike.injective f)

Depends on / 依赖: EmbeddingLike, EmbeddingLike.injective, hA.realize_comp_of_injective, injective, realize_comp_of_injective
-/
lemma IsAtomic.realize_comp {φ : L.BoundedFormula α n} (hA : φ.IsAtomic)
    [EmbeddingLike F M N] [L.HomClass F M N] (f : F) {v : α -> M} {xs : Fin n -> M} :
    φ.Realize v xs -> φ.Realize (f ∘ v) (f ∘ xs) :=
  hA.realize_comp_of_injective (EmbeddingLike.injective f)

variable [EmbeddingLike F M N] [L.StrongHomClass F M N]

/--
lemma `IsQF.realize_embedding` / 引理 `IsQF.realize_embedding`

English:
lemma IsQF.realize_embedding
  statement: {φ : L.BoundedFormula α n} (hQF : φ.IsQF)
  proof: by
  induction hQF with
  | falsum => rfl
  | of_isAtomic hA => induction hA with
    | equal t₁ t₂ => simp only [realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term,
        (EmbeddingLike.injective f).eq_iff]
    | rel R ts =>
      simp only [realize_rel, ← Sum.comp_elim, HomClass.realize_term]
      exact StrongHomClass.map_rel f R (fun i => Term.realize (Sum.elim v xs) (ts i))
  | imp _ _ ihφ ihψ => simp only [realize_imp, ihφ, ihψ]

中文:
引理 是QF.realize_embedding
  结论: {φ : L.BoundedFormula α n} (hQF : φ.是QF)
  证明: by
  induction hQF with
  | falsum => rfl
  | of_isAtomic hA => induction hA with
    | equal t₁ t₂ => simp only [realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term,
        (EmbeddingLike.injective f).eq_iff]
    | rel R ts =>
      simp only [realize_rel, ← Sum.comp_elim, HomClass.realize_term]
      exact StrongHomClass.map_rel f R (fun i => Term.realize (Sum.elim v xs) (ts i))
  | imp _ _ ihφ ihψ => simp only [realize_imp, ihφ, ihψ]

Depends on / 依赖: EmbeddingLike, EmbeddingLike.injective, HomClass, HomClass.realize_term, StrongHomClass, StrongHomClass.map_rel, Sum.comp_elim, Sum.elim, Term.realize, comp_elim, eq_iff, falsum, injective, map_rel, of_isAtomic, realize, realize_bdEqual, realize_imp, realize_rel, realize_term
-/
lemma IsQF.realize_embedding {φ : L.BoundedFormula α n} (hQF : φ.IsQF)
    (f : F) {v : α -> M} {xs : Fin n -> M} :
    φ.Realize (f ∘ v) (f ∘ xs) ↔ φ.Realize v xs := by
  induction hQF with
  | falsum => rfl
  | of_isAtomic hA => induction hA with
    | equal t₁ t₂ => simp only [realize_bdEqual, ← Sum.comp_elim, HomClass.realize_term,
        (EmbeddingLike.injective f).eq_iff]
    | rel R ts =>
      simp only [realize_rel, ← Sum.comp_elim, HomClass.realize_term]
      exact StrongHomClass.map_rel f R (fun i => Term.realize (Sum.elim v xs) (ts i))
  | imp _ _ ihφ ihψ => simp only [realize_imp, ihφ, ihψ]

/--
lemma `IsUniversal.realize_embedding` / 引理 `IsUniversal.realize_embedding`

English:
lemma IsUniversal.realize_embedding
  statement: {φ : L.BoundedFormula α n} (hU : φ.IsUniversal)
  proof: by
  induction hU with
  | of_isQF hQF => simp [hQF.realize_embedding]
  | all _ ih =>
    simp only [realize_all, Nat.succ_eq_add_one]
    refine fun h a => ih ?_
    rw [Fin.comp_snoc]
    exact h (f a)

中文:
引理 是泛.realize_embedding
  结论: {φ : L.BoundedFormula α n} (hU : φ.是泛)
  证明: by
  induction hU with
  | of_isQF hQF => simp [hQF.realize_embedding]
  | all _ ih =>
    simp only [realize_all, Nat.succ_eq_add_one]
    refine fun h a => ih ?_
    rw [Fin.comp_snoc]
    exact h (f a)

Depends on / 依赖: Fin.comp_snoc, Nat.succ_eq_add_one, comp_snoc, hQF.realize_embedding, of_isQF, realize_all, realize_embedding, succ_eq_add_one
-/
lemma IsUniversal.realize_embedding {φ : L.BoundedFormula α n} (hU : φ.IsUniversal)
    (f : F) {v : α -> M} {xs : Fin n -> M} :
    φ.Realize (f ∘ v) (f ∘ xs) -> φ.Realize v xs := by
  induction hU with
  | of_isQF hQF => simp [hQF.realize_embedding]
  | all _ ih =>
    simp only [realize_all, Nat.succ_eq_add_one]
    refine fun h a => ih ?_
    rw [Fin.comp_snoc]
    exact h (f a)

/--
lemma `IsExistential.realize_embedding` / 引理 `IsExistential.realize_embedding`

English:
lemma IsExistential.realize_embedding
  statement: {φ : L.BoundedFormula α n} (hE : φ.IsExistential)
  proof: by
  induction hE with
  | of_isQF hQF => simp [hQF.realize_embedding]
  | ex _ ih =>
    simp only [realize_ex, Nat.succ_eq_add_one]
    refine fun ⟨a, ha⟩ => ⟨f a, ?_⟩
    rw [← Fin.comp_snoc]
    exact ih ha

中文:
引理 是存在.realize_embedding
  结论: {φ : L.BoundedFormula α n} (hE : φ.是存在)
  证明: by
  induction hE with
  | of_isQF hQF => simp [hQF.realize_embedding]
  | ex _ ih =>
    simp only [realize_ex, Nat.succ_eq_add_one]
    refine fun ⟨a, ha⟩ => ⟨f a, ?_⟩
    rw [← Fin.comp_snoc]
    exact ih ha

Depends on / 依赖: Fin.comp_snoc, Nat.succ_eq_add_one, comp_snoc, hQF.realize_embedding, of_isQF, realize_embedding, realize_ex, succ_eq_add_one
-/
lemma IsExistential.realize_embedding {φ : L.BoundedFormula α n} (hE : φ.IsExistential)
    (f : F) {v : α -> M} {xs : Fin n -> M} :
    φ.Realize v xs -> φ.Realize (f ∘ v) (f ∘ xs) := by
  induction hE with
  | of_isQF hQF => simp [hQF.realize_embedding]
  | ex _ ih =>
    simp only [realize_ex, Nat.succ_eq_add_one]
    refine fun ⟨a, ha⟩ => ⟨f a, ?_⟩
    rw [← Fin.comp_snoc]
    exact ih ha

end Preservation

end BoundedFormula

/--
Definition of `Theory.IsUniversal` / `Theory.IsUniversal` 的定义

English:
class Theory.IsUniversal
  parameters: (T : L.Theory)
  axioms and operations (1):
    - isUniversal_of_mem : forall ⦃φ⦄, φ in T -> φ.IsUniversal

中文:
类 Theory.是泛
  参数: (T : L.Theory)
  公理与运算 (1 个):
    - isUniversal_of_mem : 对任意 ⦃φ⦄, φ in T -> φ.是泛
-/
class Theory.IsUniversal (T : L.Theory) : Prop where
  isUniversal_of_mem : forall ⦃φ⦄, φ in T -> φ.IsUniversal

/--
lemma `Theory.IsUniversal.models_of_embedding` / 引理 `Theory.IsUniversal.models_of_embedding`

English:
lemma Theory.IsUniversal.models_of_embedding
  statement: {T : L.Theory} [hT : T.IsUniversal]
  proof: by
  simp only [model_iff]
  refine fun φ hφ => (hT.isUniversal_of_mem hφ).realize_embedding f (?_)
  rw [Subsingleton.elim (f ∘ default) default]; rw [Subsingleton.elim (f ∘ default) default]
  exact Theory.realize_sentence_of_mem T hφ

中文:
引理 Theory.是泛.models_of_embedding
  结论: {T : L.Theory} [hT : T.是泛]
  证明: by
  simp only [model_iff]
  refine fun φ hφ => (hT.isUniversal_of_mem hφ).realize_embedding f (?_)
  rw [Subsingleton.elim (f ∘ default) default]; rw [Subsingleton.elim (f ∘ default) default]
  exact Theory.realize_sentence_of_mem T hφ

Depends on / 依赖: Subsingleton, Subsingleton.elim, Theory, Theory.realize_sentence_of_mem, hT.isUniversal_of_mem, isUniversal_of_mem, model_iff, realize_embedding, realize_sentence_of_mem
-/
lemma Theory.IsUniversal.models_of_embedding {T : L.Theory} [hT : T.IsUniversal]
    {N : Type*} [L.Structure N] [N ⊨ T] (f : M ↪[L] N) : M ⊨ T := by
  simp only [model_iff]
  refine fun φ hφ => (hT.isUniversal_of_mem hφ).realize_embedding f (?_)
  rw [Subsingleton.elim (f ∘ default) default]; rw [Subsingleton.elim (f ∘ default) default]
  exact Theory.realize_sentence_of_mem T hφ

/--
Instance `Substructure.models_of_isUniversal` / 实例 `Substructure.models_of_isUniversal`

English:
instance Substructure.models_of_isUniversal
  body: Theory.IsUniversal.models_of_embedding (Substructure.subtype S)

中文:
实例 子结构.models_of_isUniversal
  定义体: Theory.IsUniversal.models_of_embedding (Substructure.subtype S)

Depends on / 依赖: IsUniversal, Substructure, Substructure.subtype, Theory, Theory.IsUniversal.models_of_embedding, models_of_embedding, subtype
-/
instance Substructure.models_of_isUniversal
    (S : L.Substructure M) (T : L.Theory) [T.IsUniversal] [M ⊨ T] : S ⊨ T :=
  Theory.IsUniversal.models_of_embedding (Substructure.subtype S)

/--
lemma `Theory.IsUniversal.insert` / 引理 `Theory.IsUniversal.insert`

English:
lemma Theory.IsUniversal.insert
  proof: ⟨by
  simp only [Set.mem_insert_iff, forall_eq_or_imp, hφ, true_and]
  exact hT.isUniversal_of_mem⟩

中文:
引理 Theory.是泛.insert
  证明: ⟨by
  simp only [Set.mem_insert_iff, forall_eq_or_imp, hφ, true_and]
  exact hT.isUniversal_of_mem⟩

Depends on / 依赖: Set.mem_insert_iff, forall_eq_or_imp, hT.isUniversal_of_mem, isUniversal_of_mem, mem_insert_iff, true_and
-/
lemma Theory.IsUniversal.insert
    {T : L.Theory} [hT : T.IsUniversal] {φ : L.Sentence} (hφ : φ.IsUniversal) :
    (insert φ T).IsUniversal := ⟨by
  simp only [Set.mem_insert_iff, forall_eq_or_imp, hφ, true_and]
  exact hT.isUniversal_of_mem⟩

namespace Relations

open BoundedFormula

/--
lemma `isAtomic` / 引理 `isAtomic`

English:
lemma isAtomic
  given: (r : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n)))
  proof: IsAtomic.rel r ts

中文:
引理 isAtomic
  条件: (r : L.关系 l) (ts : 有限集 l -> L.项 (α oplus (有限集 n)))
  证明: IsAtomic.rel r ts

Depends on / 依赖: IsAtomic, IsAtomic.rel
-/
lemma isAtomic (r : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n))) :
    IsAtomic (r.boundedFormula ts) := IsAtomic.rel r ts

/--
lemma `isQF` / 引理 `isQF`

English:
lemma isQF
  given: (r : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n)))
  proof: (r.isAtomic ts).isQF

中文:
引理 isQF
  条件: (r : L.关系 l) (ts : 有限集 l -> L.项 (α oplus (有限集 n)))
  证明: (r.isAtomic ts).isQF

Depends on / 依赖: isAtomic, r.isAtomic
-/
lemma isQF (r : L.Relations l) (ts : Fin l -> L.Term (α oplus (Fin n))) :
    IsQF (r.boundedFormula ts) := (r.isAtomic ts).isQF

variable (r : L.Relations 2)

/--
lemma `isUniversal_reflexive` / 引理 `isUniversal_reflexive`

English:
lemma isUniversal_reflexive
  statement: r.reflexive.IsUniversal
  proof: (r.isQF _).isUniversal.all

中文:
引理 isUniversal_reflexive
  结论: r.reflexive.是泛
  证明: (r.isQF _).isUniversal.all
-/
protected lemma isUniversal_reflexive : r.reflexive.IsUniversal :=
  (r.isQF _).isUniversal.all

/--
lemma `isUniversal_irreflexive` / 引理 `isUniversal_irreflexive`

English:
lemma isUniversal_irreflexive
  statement: r.irreflexive.IsUniversal
  proof: (r.isAtomic _).isQF.not.isUniversal.all

中文:
引理 isUniversal_irreflexive
  结论: r.irreflexive.是泛
  证明: (r.isAtomic _).isQF.not.isUniversal.all
-/
protected lemma isUniversal_irreflexive : r.irreflexive.IsUniversal :=
  (r.isAtomic _).isQF.not.isUniversal.all

/--
lemma `isUniversal_symmetric` / 引理 `isUniversal_symmetric`

English:
lemma isUniversal_symmetric
  statement: r.symmetric.IsUniversal
  proof: ((r.isQF _).imp (r.isQF _)).isUniversal.all.all

中文:
引理 isUniversal_symmetric
  结论: r.symmetric.是泛
  证明: ((r.isQF _).imp (r.isQF _)).isUniversal.all.all
-/
protected lemma isUniversal_symmetric : r.symmetric.IsUniversal :=
  ((r.isQF _).imp (r.isQF _)).isUniversal.all.all

/--
lemma `isUniversal_antisymmetric` / 引理 `isUniversal_antisymmetric`

English:
lemma isUniversal_antisymmetric
  statement: r.antisymmetric.IsUniversal
  proof: ((r.isQF _).imp ((r.isQF _).imp (IsAtomic.equal _ _).isQF)).isUniversal.all.all

中文:
引理 isUniversal_antisymmetric
  结论: r.antisymmetric.是泛
  证明: ((r.isQF _).imp ((r.isQF _).imp (IsAtomic.equal _ _).isQF)).isUniversal.all.all
-/
protected lemma isUniversal_antisymmetric : r.antisymmetric.IsUniversal :=
  ((r.isQF _).imp ((r.isQF _).imp (IsAtomic.equal _ _).isQF)).isUniversal.all.all

/--
lemma `isUniversal_transitive` / 引理 `isUniversal_transitive`

English:
lemma isUniversal_transitive
  statement: r.transitive.IsUniversal
  proof: ((r.isQF _).imp ((r.isQF _).imp (r.isQF _))).isUniversal.all.all.all

中文:
引理 isUniversal_transitive
  结论: r.transitive.是泛
  证明: ((r.isQF _).imp ((r.isQF _).imp (r.isQF _))).isUniversal.all.all.all
-/
protected lemma isUniversal_transitive : r.transitive.IsUniversal :=
  ((r.isQF _).imp ((r.isQF _).imp (r.isQF _))).isUniversal.all.all.all

/--
lemma `isUniversal_total` / 引理 `isUniversal_total`

English:
lemma isUniversal_total
  statement: r.total.IsUniversal
  proof: ((r.isQF _).sup (r.isQF _)).isUniversal.all.all

中文:
引理 isUniversal_total
  结论: r.total.是泛
  证明: ((r.isQF _).sup (r.isQF _)).isUniversal.all.all
-/
protected lemma isUniversal_total : r.total.IsUniversal :=
  ((r.isQF _).sup (r.isQF _)).isUniversal.all.all

end Relations

/--
theorem `Formula.isAtomic_graph` / 定理 `Formula.isAtomic_graph`

English:
theorem Formula.isAtomic_graph
  given: (f : L.Functions n)
  statement: (Formula.graph f).IsAtomic
  proof: BoundedFormula.IsAtomic.equal _ _

中文:
定理 公式.isAtomic_graph
  条件: (f : L.函数 n)
  结论: (公式.graph f).是原子的
  证明: BoundedFormula.IsAtomic.equal _ _

Depends on / 依赖: BoundedFormula, BoundedFormula.IsAtomic.equal, IsAtomic
-/
theorem Formula.isAtomic_graph (f : L.Functions n) : (Formula.graph f).IsAtomic :=
  BoundedFormula.IsAtomic.equal _ _

end Language

end FirstOrder
