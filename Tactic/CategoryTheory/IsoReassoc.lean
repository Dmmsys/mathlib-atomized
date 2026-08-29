/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Iso

/-!
# Extension of `reassoc` to isomorphisms.

We extend `reassoc` and `reassoc_of%` for equality of isomorphisms.
Adding `@[reassoc]` to a lemma named `F` of shape `∀ .., f = g`,
where `f g : X ≅ Y` in some category will create a new lemma named `F_assoc` of shape
`∀ .. {Z : C} (h : Y ≅ Z), f ≪≫ h = g ≪≫ h`
but with the conclusions simplified using basic proportions in isomorphisms in a category
(`Iso.trans_refl`, `Iso.refl_trans`, `Iso.trans_assoc`, `Iso.trans_symm`,
`Iso.symm_self_id` and `Iso.self_symm_id`).

This is useful for generating lemmas which the simplifier can use even on expressions
that are already right associated.
-/

public meta section

open Lean Meta Elab Tactic
open CategoryTheory

namespace Mathlib.Tactic.Reassoc

/--
theorem `Iso.eq_whisker` / 定理 `Iso.eq_whisker`

English:
theorem Iso.eq_whisker
  statement: {C : Type*} [Category* C]
  proof: by rw [w]

中文:
定理 同构.eq_whisker
  结论: {C : 类型} [范畴* C]
  证明: by rw [w]

Depends on / 依赖: Icc_prod_eq, isCompact_Icc, isCompact_Icc.prod
-/
theorem Iso.eq_whisker {C : Type*} [Category* C]
    {X Y : C} {f g : X ≅ Y} (w : f = g) {Z : C} (h : Y ≅ Z) :
    f ≪≫ h = g ≪≫ h := by rw [w]

/--
Definition of `categoryIsoSimp` / `categoryIsoSimp` 的定义

English:
definition categoryIsoSimp
  signature: (e : Expr)
  body: simpOnlyNames [``Iso.trans_symm, ``Iso.trans_refl, ``Iso.refl_trans, ``Iso.trans_assoc,
    ``Iso.symm_self_id, ``Iso.self_symm_id, ``Iso.symm_self_id_assoc, ``Iso.self_symm_id_assoc,
    ``Functor.mapIso_trans, ``Functor.mapIso_symm, ``Functor.mapIso_refl, ``Functor.id_obj] e
    (config := { decid

中文:
定义 categoryIsoSimp
  签名: (e : Expr)
  定义体: simpOnlyNames [``Iso.trans_symm, ``Iso.trans_refl, ``Iso.refl_trans, ``Iso.trans_assoc,
    ``Iso.symm_self_id, ``Iso.self_symm_id, ``Iso.symm_self_id_assoc, ``Iso.self_symm_id_assoc,
    ``Functor.mapIso_trans, ``Functor.mapIso_symm, ``Functor.mapIso_refl, ``Functor.id_obj] e
    (config := { decid

Depends on / 依赖: Functor, Functor.id_obj, Functor.mapIso_refl, Functor.mapIso_symm, Functor.mapIso_trans, Iso.refl_trans, Iso.self_symm_id, Iso.self_symm_id_assoc, Iso.symm_self_id, Iso.symm_self_id_assoc, Iso.trans_assoc, Iso.trans_refl, Iso.trans_symm, config, id_obj, mapIso_refl, mapIso_symm, mapIso_trans, refl_trans, self_symm_id
-/
def categoryIsoSimp (e : Expr) : MetaM Simp.Result :=
  simpOnlyNames [``Iso.trans_symm, ``Iso.trans_refl, ``Iso.refl_trans, ``Iso.trans_assoc,
    ``Iso.symm_self_id, ``Iso.self_symm_id, ``Iso.symm_self_id_assoc, ``Iso.self_symm_id_assoc,
    ``Functor.mapIso_trans, ``Functor.mapIso_symm, ``Functor.mapIso_refl, ``Functor.id_obj] e
    (config := { decide := false })

/--
Definition of `reassocExprIso` / `reassocExprIso` 的定义

English:
definition reassocExprIso
  signature: (e : Expr)
  body: do
  let lem₀ ← mkConstWithFreshMVarLevels ``Iso.eq_whisker
  let (args, _, _) ← forallMetaBoundedTelescope (← inferType lem₀) 7
  let inst := args[1]!
  inst.mvarId!.setKind .synthetic
  let w := args[6]!
  w.mvarId!.assignIfDefEq e
  withEnsuringLocalInstance inst.mvarId! do
    return (← simpType

中文:
定义 reassocExprIso
  签名: (e : Expr)
  定义体: do
  let lem₀ ← mkConstWithFreshMVarLevels ``Iso.eq_whisker
  let (args, _, _) ← forallMetaBoundedTelescope (← inferType lem₀) 7
  let inst := args[1]!
  inst.mvarId!.setKind .synthetic
  let w := args[6]!
  w.mvarId!.assignIfDefEq e
  withEnsuringLocalInstance inst.mvarId! do
    return (← simpType

Depends on / 依赖: CompleteLinearOrder, compactSpace_of_completeLinearOrder
-/
def reassocExprIso (e : Expr) : MetaM (Expr × Array MVarId) := do
  let lem₀ ← mkConstWithFreshMVarLevels ``Iso.eq_whisker
  let (args, _, _) ← forallMetaBoundedTelescope (← inferType lem₀) 7
  let inst := args[1]!
  inst.mvarId!.setKind .synthetic
  let w := args[6]!
  w.mvarId!.assignIfDefEq e
  withEnsuringLocalInstance inst.mvarId! do
    return (← simpType categoryIsoSimp (mkAppN lem₀ args), #[inst.mvarId!])

initialize registerReassocExpr reassocExprIso

end Mathlib.Tactic.Reassoc
