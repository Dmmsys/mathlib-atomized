/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Basic

/-!
# Lemmas relating fintypes and order/lattice structure.
-/

public section


open Function

open Nat

universe u v

variable {ι α β : Type*}

namespace Finset

variable [Fintype α] {s : Finset α}

/--
theorem `sup_univ_eq_iSup` / 定理 `sup_univ_eq_iSup`

English:
theorem sup_univ_eq_iSup
  given: [CompleteLattice β] (f : α -> β)
  statement: Finset.univ.sup f = iSup f
  proof: (sup_eq_iSup _ f).trans congr_arg _ funext fun _ => iSup_pos (mem_univ _)

中文:
定理 sup_univ_eq_iSup
  条件: [完备格 β] (f : α -> β)
  结论: 有限集.univ.上确界 f = iSup f
  证明: (sup_eq_iSup _ f).trans congr_arg _ funext fun _ => iSup_pos (mem_univ _)

Depends on / 依赖: congr_arg, iSup_pos, mem_univ, sup_eq_iSup
-/
theorem sup_univ_eq_iSup [CompleteLattice β] (f : α -> β) : Finset.univ.sup f = iSup f :=
(sup_eq_iSup _ f).trans congr_arg _ funext fun _ => iSup_pos (mem_univ _)

/--
theorem `inf_univ_eq_iInf` / 定理 `inf_univ_eq_iInf`

English:
theorem inf_univ_eq_iInf
  given: [CompleteLattice β] (f : α -> β)
  statement: Finset.univ.inf f = iInf f
  proof: @sup_univ_eq_iSup _ βᵒᵈ _ _ (f : α -> βᵒᵈ)

@[simp]

中文:
定理 inf_univ_eq_iInf
  条件: [完备格 β] (f : α -> β)
  结论: 有限集.univ.下确界 f = iInf f
  证明: @sup_univ_eq_iSup _ βᵒᵈ _ _ (f : α -> βᵒᵈ)

@[simp]

Depends on / 依赖: sup_univ_eq_iSup
-/
theorem inf_univ_eq_iInf [CompleteLattice β] (f : α -> β) : Finset.univ.inf f = iInf f :=
  @sup_univ_eq_iSup _ βᵒᵈ _ _ (f : α -> βᵒᵈ)

@[simp]
/--
theorem `fold_inf_univ` / 定理 `fold_inf_univ`

English:
theorem fold_inf_univ
  given: [SemilatticeInf α] [OrderBot α] (a : α)
  proof: eq_bot_iff.2
((Finset.fold_op_rel_iff_and <| @le_inf_iff α _).1 le_rfl).2 ⊥ Finset.mem_univ _

@[simp]

中文:
定理 fold_inf_univ
  条件: [SemilatticeInf α] [有底序 α] (a : α)
  证明: eq_bot_iff.2
((Finset.fold_op_rel_iff_and <| @le_inf_iff α _).1 le_rfl).2 ⊥ Finset.mem_univ _

@[simp]

Depends on / 依赖: Finset, Finset.fold_op_rel_iff_and, Finset.mem_univ, eq_bot_iff, fold_op_rel_iff_and, le_inf_iff, le_rfl, mem_univ
-/
theorem fold_inf_univ [SemilatticeInf α] [OrderBot α] (a : α) :
    (Finset.univ.fold min a fun x => x) = ⊥ :=
eq_bot_iff.2
((Finset.fold_op_rel_iff_and <| @le_inf_iff α _).1 le_rfl).2 ⊥ Finset.mem_univ _

@[simp]
/--
theorem `fold_sup_univ` / 定理 `fold_sup_univ`

English:
theorem fold_sup_univ
  given: [SemilatticeSup α] [OrderTop α] (a : α)
  proof: @fold_inf_univ αᵒᵈ _ _ _ _

中文:
定理 fold_sup_univ
  条件: [SemilatticeSup α] [有顶序 α] (a : α)
  证明: @fold_inf_univ αᵒᵈ _ _ _ _

Depends on / 依赖: fold_inf_univ
-/
theorem fold_sup_univ [SemilatticeSup α] [OrderTop α] (a : α) :
    (Finset.univ.fold max a fun x => x) = ⊤ :=
  @fold_inf_univ αᵒᵈ _ _ _ _

/--
lemma `mem_inf` / 引理 `mem_inf`

English:
lemma mem_inf
  given: [DecidableEq α] {s : Finset ι} {f : ι -> Finset α} {a : α}
  proof: by induction s using Finset.cons_induction <;> simp [*]

中文:
引理 mem_inf
  条件: [DecidableEq α] {s : 有限集 ι} {f : ι -> 有限集 α} {a : α}
  证明: by induction s using Finset.cons_induction <;> simp [*]

Depends on / 依赖: Finset, Finset.cons_induction, cons_induction
-/
lemma mem_inf [DecidableEq α] {s : Finset ι} {f : ι -> Finset α} {a : α} :
    a in s.inf f ↔ forall i in s, a in f i := by induction s using Finset.cons_induction <;> simp [*]

end Finset

open Finset

/--
theorem `Finite.exists_max` / 定理 `Finite.exists_max`

English:
theorem Finite.exists_max
  given: [Finite α] [Nonempty α] [LinearOrder β] (f : α -> β)
  proof: by
  cases nonempty_fintype α
  simpa using exists_max_image univ f univ_nonempty

中文:
定理 有限.存在_max
  条件: [有限 α] [非空 α] [线性序 β] (f : α -> β)
  证明: by
  cases nonempty_fintype α
  simpa using exists_max_image univ f univ_nonempty

Depends on / 依赖: exists_max_image, nonempty_fintype, univ_nonempty
-/
theorem Finite.exists_max [Finite α] [Nonempty α] [LinearOrder β] (f : α -> β) :
    exists x₀ : α, forall x, f x <= f x₀ := by
  cases nonempty_fintype α
  simpa using exists_max_image univ f univ_nonempty

/--
theorem `Finite.exists_min` / 定理 `Finite.exists_min`

English:
theorem Finite.exists_min
  given: [Finite α] [Nonempty α] [LinearOrder β] (f : α -> β)
  proof: by
  cases nonempty_fintype α
  simpa using exists_min_image univ f univ_nonempty

中文:
定理 有限.存在_min
  条件: [有限 α] [非空 α] [线性序 β] (f : α -> β)
  证明: by
  cases nonempty_fintype α
  simpa using exists_min_image univ f univ_nonempty

Depends on / 依赖: exists_min_image, nonempty_fintype, univ_nonempty
-/
theorem Finite.exists_min [Finite α] [Nonempty α] [LinearOrder β] (f : α -> β) :
    exists x₀ : α, forall x, f x₀ <= f x := by
  cases nonempty_fintype α
  simpa using exists_min_image univ f univ_nonempty
