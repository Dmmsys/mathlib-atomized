/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
import Mathlib.Order.Preorder.Finite

/-!
# Binary product of standard simplices

In this file, we show that `Δ[p] ⊗ Δ[q]` identifies to the nerve of
`ULift (Fin (p + 1) × Fin (q + 1))`. We relate the `n`-simplices
of `Δ[p] ⊗ Δ[q]` to order preserving maps `Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`,
Via this bijection, a simplex in `Δ[p] ⊗ Δ[q]` is nondegenerate iff
the corresponding monotone map `Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`
is injective (or a strict mono).

We also show that the dimension of `Δ[p] ⊗ Δ[q]` is `≤ p + q`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial MonoidalCategory

namespace SSet

namespace prodStdSimplex

variable {p q : Nat}

/--
Definition of `objEquiv` / `objEquiv` 的定义

English:
definition objEquiv
  signature: {n : Nat}
  body: fun ⟨x, y⟩ => OrderHom.prod
      (stdSimplex.objEquiv x).toOrderHom
      (stdSimplex.objEquiv y).toOrderHom
  invFun f :=
    ⟨stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.fst.comp f)),
      stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.snd.comp f))⟩
  left_inv := fun ⟨x, y⟩ => by simp

@[simp]

中文:
定义 objEquiv
  签名: {n : 自然数}
  定义体: fun ⟨x, y⟩ => OrderHom.prod
      (stdSimplex.objEquiv x).toOrderHom
      (stdSimplex.objEquiv y).toOrderHom
  invFun f :=
    ⟨stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.fst.comp f)),
      stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.snd.comp f))⟩
  left_inv := fun ⟨x, y⟩ => by simp

@[simp]

Depends on / 依赖: OrderHom, OrderHom.prod
-/
def objEquiv {n : Nat} :
    (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌ ≃ (Fin (n + 1) ->o Fin (p + 1) × Fin (q + 1)) where
  toFun := fun ⟨x, y⟩ => OrderHom.prod
      (stdSimplex.objEquiv x).toOrderHom
      (stdSimplex.objEquiv y).toOrderHom
  invFun f :=
    ⟨stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.fst.comp f)),
      stdSimplex.objEquiv.symm
      (SimplexCategory.Hom.mk (OrderHom.snd.comp f))⟩
  left_inv := fun ⟨x, y⟩ => by simp

@[simp]
/--
lemma `objEquiv_apply_fst` / 引理 `objEquiv_apply_fst`

English:
lemma objEquiv_apply_fst
  given: {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1))
  proof: rfl

@[simp]

中文:
引理 objEquiv_apply_fst
  条件: {n : 自然数} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) (i : 有限集 (n + 1))
  证明: rfl

@[simp]
-/
lemma objEquiv_apply_fst {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1)) :
    dsimp% (objEquiv x i).1 = x.1 i := rfl

@[simp]
/--
lemma `objEquiv_apply_snd` / 引理 `objEquiv_apply_snd`

English:
lemma objEquiv_apply_snd
  given: {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1))
  proof: rfl

中文:
引理 objEquiv_apply_snd
  条件: {n : 自然数} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) (i : 有限集 (n + 1))
  证明: rfl
-/
lemma objEquiv_apply_snd {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) (i : Fin (n + 1)) :
    dsimp% (objEquiv x i).2 = x.2 i := rfl

/--
lemma `objEquiv_naturality` / 引理 `objEquiv_naturality`

English:
lemma objEquiv_naturality
  statement: {m n : Nat} (f : ⦋m⦌ ⟶ ⦋n⦌)
  proof: rfl

中文:
引理 objEquiv_naturality
  结论: {m n : 自然数} (f : ⦋m⦌ ⟶ ⦋n⦌)
  证明: rfl
-/
lemma objEquiv_naturality {m n : Nat} (f : ⦋m⦌ ⟶ ⦋n⦌)
    (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) :
    (objEquiv z).comp f.toOrderHom = objEquiv ((Δ[p] otimes Δ[q]).map f.op z) :=
  rfl

/--
lemma `objEquiv_map_apply` / 引理 `objEquiv_map_apply`

English:
lemma objEquiv_map_apply
  statement: {n m : Nat}
  proof: rfl

中文:
引理 objEquiv_map_apply
  结论: {n m : 自然数}
  证明: rfl
-/
lemma objEquiv_map_apply {n m : Nat}
    (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) (f : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
      objEquiv ((Δ[p] otimes Δ[q]).map f.op x) i = objEquiv x (f.toOrderHom i) :=
  rfl

/--
lemma `objEquiv_δ_apply` / 引理 `objEquiv_δ_apply`

English:
lemma objEquiv_δ_apply
  statement: {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n + 1⦌) (i : Fin (n + 2))
  proof: rfl

中文:
引理 objEquiv_δ_apply
  结论: {n : 自然数} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n + 1⦌) (i : 有限集 (n + 2))
  证明: rfl
-/
lemma objEquiv_δ_apply {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n + 1⦌) (i : Fin (n + 2))
    (j : Fin (n + 1)) :
    objEquiv ((Δ[p] otimes Δ[q]).δ i x) j = objEquiv x (i.succAbove j) := rfl

variable (p q) in
/--
Definition of `isoNerve` / `isoNerve` 的定义

English:
definition isoNerve
  signature: : Δ[p] otimes Δ[q] ≅ nerve (ULift.{u} (Fin (p + 1) × Fin (q + 1)))
  body: NatIso.ofComponents (fun ⟨⟨d⟩⟩ => Equiv.toIso (objEquiv.trans
      { toFun f := (ULift.orderIso.symm.monotone.comp f.monotone).functor
        invFun s := ULift.orderIso.toOrderEmbedding.toOrderHom.comp ⟨_, s.monotone⟩ }))

中文:
定义 isoNerve
  签名: : Δ[p] otimes Δ[q] ≅ nerve (类型层提升.{u} (有限集 (p + 1) × 有限集 (q + 1)))
  定义体: NatIso.ofComponents (fun ⟨⟨d⟩⟩ => Equiv.toIso (objEquiv.trans
      { toFun f := (ULift.orderIso.symm.monotone.comp f.monotone).functor
        invFun s := ULift.orderIso.toOrderEmbedding.toOrderHom.comp ⟨_, s.monotone⟩ }))

Depends on / 依赖: Equiv.toIso, NatIso, NatIso.ofComponents, ULift.orderIso.symm.monotone.comp, ULift.orderIso.toOrderEmbedding.toOrderHom.comp, f.monotone, functor, invFun, monotone, objEquiv, objEquiv.trans, ofComponents, orderIso, s.monotone, toOrderEmbedding, toOrderHom
-/
def isoNerve : Δ[p] otimes Δ[q] ≅ nerve (ULift.{u} (Fin (p + 1) × Fin (q + 1))) :=
  NatIso.ofComponents (fun ⟨⟨d⟩⟩ => Equiv.toIso (objEquiv.trans
      { toFun f := (ULift.orderIso.symm.monotone.comp f.monotone).functor
        invFun s := ULift.orderIso.toOrderEmbedding.toOrderHom.comp ⟨_, s.monotone⟩ }))

/--
lemma `nonDegenerate_iff_injective_objEquiv` / 引理 `nonDegenerate_iff_injective_objEquiv`

English:
lemma nonDegenerate_iff_injective_objEquiv
  given: {n : Nat} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌)
  proof: by
  rw [← nonDegenerate_iff_of_mono (isoNerve p q).hom]; rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective]; rw [← Function.Injective.of_comp_iff ULift.down_injective]
  rfl

中文:
引理 nonDegenerate_iff_injective_objEquiv
  条件: {n : 自然数} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌)
  证明: by
  rw [← nonDegenerate_iff_of_mono (isoNerve p q).hom]; rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective]; rw [← Function.Injective.of_comp_iff ULift.down_injective]
  rfl

Depends on / 依赖: Function, Function.Injective.of_comp_iff, Injective, PartialOrder, PartialOrder.mem_nerve_nonDegenerate_iff_injective, ULift.down_injective, down_injective, isoNerve, mem_nerve_nonDegenerate_iff_injective, nonDegenerate_iff_of_mono, of_comp_iff
-/
lemma nonDegenerate_iff_injective_objEquiv {n : Nat} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) :
    z in (Δ[p] otimes Δ[q]).nonDegenerate n ↔ Function.Injective (objEquiv z) := by
  rw [← nonDegenerate_iff_of_mono (isoNerve p q).hom]; rw [PartialOrder.mem_nerve_nonDegenerate_iff_injective]; rw [← Function.Injective.of_comp_iff ULift.down_injective]
  rfl

/--
lemma `nonDegenerate_iff_strictMono_objEquiv` / 引理 `nonDegenerate_iff_strictMono_objEquiv`

English:
lemma nonDegenerate_iff_strictMono_objEquiv
  given: {n : Nat} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌)
  proof: by
  rw [← nonDegenerate_iff_of_mono (isoNerve p q).hom]; rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  rfl

中文:
引理 nonDegenerate_iff_strictMono_objEquiv
  条件: {n : 自然数} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌)
  证明: by
  rw [← nonDegenerate_iff_of_mono (isoNerve p q).hom]; rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  rfl

Depends on / 依赖: PartialOrder, PartialOrder.mem_nerve_nonDegenerate_iff_strictMono, isoNerve, mem_nerve_nonDegenerate_iff_strictMono, nonDegenerate_iff_of_mono
-/
lemma nonDegenerate_iff_strictMono_objEquiv {n : Nat} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) :
    z in (Δ[p] otimes Δ[q]).nonDegenerate n ↔ StrictMono (objEquiv z) := by
  rw [← nonDegenerate_iff_of_mono (isoNerve p q).hom]; rw [PartialOrder.mem_nerve_nonDegenerate_iff_strictMono]
  rfl

/-- Given a `n`-simplex `x` in `Δ[p] ⊗ Δ[q]`, this is the order preserving
map `Fin (n + 1) →o Fin (m + 1)` (with `p + q = m`) which corresponds to the
sum of the two components of `objEquiv x : Fin (n + 1) →o Fin (p + 1) × Fin (q + 1)`. -/
@[simps coe]
/--
Definition of `orderHomOfSimplex` / `orderHomOfSimplex` 的定义

English:
definition orderHomOfSimplex
  signature: {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) {m : Nat} (hm : p + q = m)
  body: ⟨(x.1 i : Nat) + x.2 i, by lia⟩
  monotone' i j h := by
    dsimp
    simp only [Fin.mk_le_mk]
    have := (objEquiv x).monotone h
    have h₁ : x.1 i <= x.1 j := this.1
    have h₂ : x.2 i <= x.2 j := this.2
    lia

中文:
定义 orderHomOfSimplex
  签名: {n : 自然数} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) {m : 自然数} (hm : p + q = m)
  定义体: ⟨(x.1 i : Nat) + x.2 i, by lia⟩
  monotone' i j h := by
    dsimp
    simp only [Fin.mk_le_mk]
    have := (objEquiv x).monotone h
    have h₁ : x.1 i <= x.1 j := this.1
    have h₂ : x.2 i <= x.2 j := this.2
    lia
-/
def orderHomOfSimplex {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) {m : Nat} (hm : p + q = m) :
    Fin (n + 1) ->o Fin (m + 1) where
  toFun i := ⟨(x.1 i : Nat) + x.2 i, by lia⟩
  monotone' i j h := by
    dsimp
    simp only [Fin.mk_le_mk]
    have := (objEquiv x).monotone h
    have h₁ : x.1 i <= x.1 j := this.1
    have h₂ : x.2 i <= x.2 j := this.2
    lia

/--
lemma `strictMono_orderHomOfSimplex_iff` / 引理 `strictMono_orderHomOfSimplex_iff`

English:
lemma strictMono_orderHomOfSimplex_iff
  statement: {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) {m : Nat}
  proof: by
  have (a b : Fin (p + 1) × Fin (q + 1)) (hab : a <= b) :
      a < b ↔ ((a.1 : Nat) + a.2 < (b.1 : Nat) + b.2) := by
    obtain ⟨h₁, h₂⟩ := hab
    rw [Prod.lt_iff]
    lia
  simp only [Fin.strictMono_iff_lt_succ]
  exact forall_congr' (fun i => (this _ _ ((objEquiv x).monotone i.castSucc_le_succ)).symm)

中文:
引理 strictMono_orderHomOfSimplex_iff
  结论: {n : 自然数} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) {m : 自然数}
  证明: by
  have (a b : Fin (p + 1) × Fin (q + 1)) (hab : a <= b) :
      a < b ↔ ((a.1 : Nat) + a.2 < (b.1 : Nat) + b.2) := by
    obtain ⟨h₁, h₂⟩ := hab
    rw [Prod.lt_iff]
    lia
  simp only [Fin.strictMono_iff_lt_succ]
  exact forall_congr' (fun i => (this _ _ ((objEquiv x).monotone i.castSucc_le_succ)).symm)

Depends on / 依赖: Fin.strictMono_iff_lt_succ, Prod.lt_iff, castSucc_le_succ, forall_congr, i.castSucc_le_succ, lt_iff, monotone, objEquiv, strictMono_iff_lt_succ
-/
lemma strictMono_orderHomOfSimplex_iff {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌) {m : Nat}
    (hm : p + q = m) :
    StrictMono (orderHomOfSimplex x hm) ↔ StrictMono (objEquiv x) := by
  have (a b : Fin (p + 1) × Fin (q + 1)) (hab : a <= b) :
      a < b ↔ ((a.1 : Nat) + a.2 < (b.1 : Nat) + b.2) := by
    obtain ⟨h₁, h₂⟩ := hab
    rw [Prod.lt_iff]
    lia
  simp only [Fin.strictMono_iff_lt_succ]
  exact forall_congr' (fun i => (this _ _ ((objEquiv x).monotone i.castSucc_le_succ)).symm)

/--
lemma `strictMono_orderHomOfSimplex` / 引理 `strictMono_orderHomOfSimplex`

English:
lemma strictMono_orderHomOfSimplex
  statement: {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n) {m : Nat}
  proof: by
  simpa only [strictMono_orderHomOfSimplex_iff, ← nonDegenerate_iff_strictMono_objEquiv] using x.2

中文:
引理 strictMono_orderHomOfSimplex
  结论: {n : 自然数} (x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n) {m : 自然数}
  证明: by
  simpa only [strictMono_orderHomOfSimplex_iff, ← nonDegenerate_iff_strictMono_objEquiv] using x.2

Depends on / 依赖: nonDegenerate_iff_strictMono_objEquiv, strictMono_orderHomOfSimplex_iff
-/
lemma strictMono_orderHomOfSimplex {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n) {m : Nat}
    (hm : p + q = m) :
    StrictMono (orderHomOfSimplex x.1 hm) := by
  simpa only [strictMono_orderHomOfSimplex_iff, ← nonDegenerate_iff_strictMono_objEquiv] using x.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Δ[p] otimes Δ[q] : SSet.{u}).HasDimensionLE (p + q)
  body: by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    by_contra hx
    rw [← mem_nonDegenerate_iff_notMem_degenerate]; rw [nonDegenerate_iff_strictMono_objEquiv]; rw [← strictMono_orderHomOfSimplex_iff _ rfl] at hx
    replace hx := Fintype.card_le_of_injective _ hx.injective
    simp only [Fintype.card_fin, add_le_add_iff_right] at hx
    lia

中文:
实例 :
  签名: (Δ[p] otimes Δ[q] : SSet.{u}).HasDimensionLE (p + q)
  定义体: by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    by_contra hx
    rw [← mem_nonDegenerate_iff_notMem_degenerate]; rw [nonDegenerate_iff_strictMono_objEquiv]; rw [← strictMono_orderHomOfSimplex_iff _ rfl] at hx
    replace hx := Fintype.card_le_of_injective _ hx.injective
    simp only [Fintype.card_fin, add_le_add_iff_right] at hx
    lia

Depends on / 依赖: Fintype, Fintype.card_fin, Fintype.card_le_of_injective, Set.mem_univ, Set.top_eq_univ, add_le_add_iff_right, card_fin, card_le_of_injective, hx.injective, iff_true, injective, mem_nonDegenerate_iff_notMem_degenerate, mem_univ, nonDegenerate_iff_strictMono_objEquiv, replace, strictMono_orderHomOfSimplex_iff, top_eq_univ
-/
instance : (Δ[p] otimes Δ[q] : SSet.{u}).HasDimensionLE (p + q) where
  degenerate_eq_top n hn := by
    ext x
    simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
    by_contra hx
    rw [← mem_nonDegenerate_iff_notMem_degenerate]; rw [nonDegenerate_iff_strictMono_objEquiv]; rw [← strictMono_orderHomOfSimplex_iff _ rfl] at hx
    replace hx := Fintype.card_le_of_injective _ hx.injective
    simp only [Fintype.card_fin, add_le_add_iff_right] at hx
    lia

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (Δ[p] otimes Δ[q] : SSet.{u}).Finite
  body: finite_of_hasDimensionLT _ (p + q + 1) inferInstance

中文:
实例 :
  签名: (Δ[p] otimes Δ[q] : SSet.{u}).有限
  定义体: finite_of_hasDimensionLT _ (p + q + 1) inferInstance

Depends on / 依赖: finite_of_hasDimensionLT
-/
instance : (Δ[p] otimes Δ[q] : SSet.{u}).Finite :=
  finite_of_hasDimensionLT _ (p + q + 1) inferInstance

/--
lemma `le_orderHomOfSimplex` / 引理 `le_orderHomOfSimplex`

English:
lemma le_orderHomOfSimplex
  statement: {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n) {m : Nat}
  proof: by
  induction i using Fin.induction with
  | zero => simp
  | succ i hi =>
    simpa using! lt_of_le_of_lt hi (strictMono_orderHomOfSimplex x hm Fin.castSucc_lt_succ)

中文:
引理 le_orderHomOfSimplex
  结论: {n : 自然数} (x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n) {m : 自然数}
  证明: by
  induction i using Fin.induction with
  | zero => simp
  | succ i hi =>
    simpa using! lt_of_le_of_lt hi (strictMono_orderHomOfSimplex x hm Fin.castSucc_lt_succ)

Depends on / 依赖: Fin.castSucc_lt_succ, Fin.induction, castSucc_lt_succ, lt_of_le_of_lt, strictMono_orderHomOfSimplex
-/
lemma le_orderHomOfSimplex {n : Nat} (x : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n) {m : Nat}
    (hm : p + q = m) (i : Fin (n + 1)) : i.1 <= orderHomOfSimplex x.1 hm i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i hi =>
    simpa using! lt_of_le_of_lt hi (strictMono_orderHomOfSimplex x hm Fin.castSucc_lt_succ)

/--
lemma `nonDegenerate_max_dim_iff` / 引理 `nonDegenerate_max_dim_iff`

English:
lemma nonDegenerate_max_dim_iff
  statement: {n : Nat} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌)
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · exact OrderHom.eq_id_of_injective _ (strictMono_orderHomOfSimplex ⟨z, h⟩ hn).injective
  · rw [nonDegenerate_iff_injective_objEquiv]
    intro h a b hab
    simp only [DFunLike.ext_iff, orderHomOfSimplex_coe, OrderHom.id_coe, id_eq] at h
    rw [← h a]; rw [← h b]; rw [Fin.ext_iff]
    change ((objEquiv z a).1 : Nat) + (objEquiv z a).2 = (objEquiv z b).1 + (objEquiv z b).2
    simp only [hab]

中文:
引理 nonDegenerate_max_dim_iff
  结论: {n : 自然数} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌)
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · exact OrderHom.eq_id_of_injective _ (strictMono_orderHomOfSimplex ⟨z, h⟩ hn).injective
  · rw [nonDegenerate_iff_injective_objEquiv]
    intro h a b hab
    simp only [DFunLike.ext_iff, orderHomOfSimplex_coe, OrderHom.id_coe, id_eq] at h
    rw [← h a]; rw [← h b]; rw [Fin.ext_iff]
    change ((objEquiv z a).1 : Nat) + (objEquiv z a).2 = (objEquiv z b).1 + (objEquiv z b).2
    simp only [hab]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Fin.ext_iff, OrderHom, OrderHom.eq_id_of_injective, OrderHom.id_coe, eq_id_of_injective, ext_iff, id_coe, id_eq, injective, nonDegenerate, nonDegenerate_iff_injective_objEquiv, objEquiv, orderHomOfSimplex, orderHomOfSimplex_coe, otimes, strictMono_orderHomOfSimplex
-/
lemma nonDegenerate_max_dim_iff {n : Nat} (z : (Δ[p] otimes Δ[q] : SSet.{u}) _⦋n⦌)
    (hn : p + q = n := by lia) :
    z in (Δ[p] otimes Δ[q]).nonDegenerate n ↔ orderHomOfSimplex z hn = .id := by
  refine ⟨fun h => ?_, ?_⟩
  · exact OrderHom.eq_id_of_injective _ (strictMono_orderHomOfSimplex ⟨z, h⟩ hn).injective
  · rw [nonDegenerate_iff_injective_objEquiv]
    intro h a b hab
    simp only [DFunLike.ext_iff, orderHomOfSimplex_coe, OrderHom.id_coe, id_eq] at h
    rw [← h a]; rw [← h b]; rw [Fin.ext_iff]
    change ((objEquiv z a).1 : Nat) + (objEquiv z a).2 = (objEquiv z b).1 + (objEquiv z b).2
    simp only [hab]

/--
lemma `nonDegenerate_ext₁` / 引理 `nonDegenerate_ext₁`

English:
lemma nonDegenerate_ext₁
  statement: {n : Nat} {z₁ z₂ : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n}
  proof: by
  ext
  apply objEquiv.injective
  ext i : 3
  · exact DFunLike.congr_fun h i
  · have h₁ := z₁.2
    have h₂ := z₂.2
    rw [nonDegenerate_max_dim_iff] at h₁ h₂
    simpa only [orderHomOfSimplex_coe, h, Fin.ext_iff, add_right_inj]
      using! DFunLike.congr_fun (h₁.trans h₂.symm) i

中文:
引理 nonDegenerate_ext₁
  结论: {n : 自然数} {z₁ z₂ : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n}
  证明: by
  ext
  apply objEquiv.injective
  ext i : 3
  · exact DFunLike.congr_fun h i
  · have h₁ := z₁.2
    have h₂ := z₂.2
    rw [nonDegenerate_max_dim_iff] at h₁ h₂
    simpa only [orderHomOfSimplex_coe, h, Fin.ext_iff, add_right_inj]
      using! DFunLike.congr_fun (h₁.trans h₂.symm) i

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Fin.ext_iff, add_right_inj, congr_fun, ext_iff, injective, nonDegenerate_max_dim_iff, objEquiv, objEquiv.injective, orderHomOfSimplex_coe
-/
lemma nonDegenerate_ext₁ {n : Nat} {z₁ z₂ : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n}
    (h : z₁.1.1 = z₂.1.1) (hn : p + q = n := by lia) :
    z₁ = z₂ := by
  ext
  apply objEquiv.injective
  ext i : 3
  · exact DFunLike.congr_fun h i
  · have h₁ := z₁.2
    have h₂ := z₂.2
    rw [nonDegenerate_max_dim_iff] at h₁ h₂
    simpa only [orderHomOfSimplex_coe, h, Fin.ext_iff, add_right_inj]
      using! DFunLike.congr_fun (h₁.trans h₂.symm) i

/--
lemma `nonDegenerate_ext₂` / 引理 `nonDegenerate_ext₂`

English:
lemma nonDegenerate_ext₂
  statement: {n : Nat} {z₁ z₂ : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n}
  proof: (nonDegenerateEquivOfIso (β_ _ _)).injective (nonDegenerate_ext₁ h)

中文:
引理 nonDegenerate_ext₂
  结论: {n : 自然数} {z₁ z₂ : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n}
  证明: (nonDegenerateEquivOfIso (β_ _ _)).injective (nonDegenerate_ext₁ h)

Depends on / 依赖: injective, nonDegenerateEquivOfIso
-/
lemma nonDegenerate_ext₂ {n : Nat} {z₁ z₂ : (Δ[p] otimes Δ[q] : SSet.{u}).nonDegenerate n}
    (h : z₁.1.2 = z₂.1.2) (hn : p + q = n := by lia) :
    z₁ = z₂ :=
  (nonDegenerateEquivOfIso (β_ _ _)).injective (nonDegenerate_ext₁ h)

end prodStdSimplex

end SSet
