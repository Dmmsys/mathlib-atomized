/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Tactic.Field

/-!
# Bases in a vector space

This file provides results for bases of a vector space.

Some of these results should be merged with the results on free modules.
We state these results in a separate file to the results on modules to avoid an
import cycle.

## Main statements

* `Basis.ofVectorSpace` states that every vector space has a basis.
* `Module.Free.of_divisionRing` states that every vector space is a free module.

## Tags

basis, bases

-/

@[expose] public section

open Function Module Set Submodule

variable {ι : Type*} {ι' : Type*} {K : Type*} {V : Type*} {V' : Type*}

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [AddCommGroup V'] [Module K V] [Module K V']
variable {v : ι -> V} {s t : Set V} {x y z : V}

open Submodule

namespace Module.Basis

section ExistsBasis

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (hs : LinearIndepOn K id s)
  body: Basis.mk
    (hs.linearIndepOn_extend _).linearIndependent_restrict
    (SetLike.coe_subset_coe.mp <| by simpa using hs.subset_span_extend (subset_univ s))

中文:
定义 extend
  签名: (hs : LinearIndepOn K id s)
  定义体: Basis.mk
    (hs.linearIndepOn_extend _).linearIndependent_restrict
    (SetLike.coe_subset_coe.mp <| by simpa using hs.subset_span_extend (subset_univ s))

Depends on / 依赖: Basis.mk, SetLike, SetLike.coe_subset_coe.mp, coe_subset_coe, hs.linearIndepOn_extend, hs.subset_span_extend, linearIndepOn_extend, linearIndependent_restrict, subset_span_extend, subset_univ
-/
noncomputable def extend (hs : LinearIndepOn K id s) :
    Basis (hs.extend (subset_univ s)) K V :=
  Basis.mk
    (hs.linearIndepOn_extend _).linearIndependent_restrict
    (SetLike.coe_subset_coe.mp <| by simpa using hs.subset_span_extend (subset_univ s))

/--
theorem `extend_apply_self` / 定理 `extend_apply_self`

English:
theorem extend_apply_self
  given: (hs : LinearIndepOn K id s) (x : hs.extend _)
  statement: Basis.extend hs x = x
  proof: Basis.mk_apply _ _ _

@[simp]

中文:
定理 extend_apply_self
  条件: (hs : LinearIndepOn K id s) (x : hs.extend _)
  结论: Basis.extend hs x = x
  证明: Basis.mk_apply _ _ _

@[simp]

Depends on / 依赖: Basis.mk_apply, mk_apply
-/
theorem extend_apply_self (hs : LinearIndepOn K id s) (x : hs.extend _) : Basis.extend hs x = x :=
  Basis.mk_apply _ _ _

@[simp]
/--
theorem `coe_extend` / 定理 `coe_extend`

English:
theorem coe_extend
  given: (hs : LinearIndepOn K id s)
  statement: ⇑(Basis.extend hs) = ((↑) : _ -> _)
  proof: funext (extend_apply_self hs)

中文:
定理 coe_extend
  条件: (hs : LinearIndepOn K id s)
  结论: ⇑(Basis.extend hs) = ((↑) : _ -> _)
  证明: funext (extend_apply_self hs)

Depends on / 依赖: extend_apply_self
-/
theorem coe_extend (hs : LinearIndepOn K id s) : ⇑(Basis.extend hs) = ((↑) : _ -> _) :=
  funext (extend_apply_self hs)

/--
theorem `range_extend` / 定理 `range_extend`

English:
theorem range_extend
  given: (hs : LinearIndepOn K id s)
  proof: by
  rw [coe_extend]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

中文:
定理 range_extend
  条件: (hs : LinearIndepOn K id s)
  证明: by
  rw [coe_extend]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, coe_extend, ofPred_mem_eq, range_coe_subtype
-/
theorem range_extend (hs : LinearIndepOn K id s) :
    range (Basis.extend hs) = hs.extend (subset_univ _) := by
  rw [coe_extend]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `sumExtendIndex` / `sumExtendIndex` 的定义

English:
definition sumExtendIndex
  signature: (hs : LinearIndependent K v)
  body: LinearIndepOn.extend hs.linearIndepOn_id (subset_univ _) \ range v

中文:
定义 sumExtendIndex
  签名: (hs : LinearIndependent K v)
  定义体: LinearIndepOn.extend hs.linearIndepOn_id (subset_univ _) \ range v

Depends on / 依赖: LinearIndepOn, LinearIndepOn.extend, extend, hs.linearIndepOn_id, linearIndepOn_id, subset_univ
-/
noncomputable def sumExtendIndex (hs : LinearIndependent K v) : Set V :=
  LinearIndepOn.extend hs.linearIndepOn_id (subset_univ _) \ range v

/--
Definition of `sumExtend` / `sumExtend` 的定义

English:
definition sumExtend
  signature: (hs : LinearIndependent K v)
  body: let s := Set.range v
  let e : ι ≃ s := Equiv.ofInjective v hs.injective
  let b := hs.linearIndepOn_id.extend (subset_univ (Set.range v))
(Basis.extend hs.linearIndepOn_id).reindex
Equiv.symm
      calc
        ι oplus (b \ s : Set V) ≃ s oplus (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
   

中文:
定义 sumExtend
  签名: (hs : LinearIndependent K v)
  定义体: let s := Set.range v
  let e : ι ≃ s := Equiv.ofInjective v hs.injective
  let b := hs.linearIndepOn_id.extend (subset_univ (Set.range v))
(Basis.extend hs.linearIndepOn_id).reindex
Equiv.symm
      calc
        ι oplus (b \ s : Set V) ≃ s oplus (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
   

Depends on / 依赖: Basis.extend, Classical, Classical.decPred, Equiv.Set.sumDiffSubset, Equiv.ofInjective, Equiv.refl, Equiv.sumCongr, Equiv.symm, Set.range, decPred, extend, hs.injective, hs.linearIndepOn_id, hs.linearIndepOn_id.extend, hs.linearIndepOn_id.subset_extend, injective, linearIndepOn_id, ofInjective, reindex, subset_extend
-/
noncomputable def sumExtend (hs : LinearIndependent K v) : Basis (ι oplus sumExtendIndex hs) K V :=
  let s := Set.range v
  let e : ι ≃ s := Equiv.ofInjective v hs.injective
  let b := hs.linearIndepOn_id.extend (subset_univ (Set.range v))
(Basis.extend hs.linearIndepOn_id).reindex
Equiv.symm
      calc
        ι oplus (b \ s : Set V) ≃ s oplus (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
        _ ≃ b :=
          haveI := Classical.decPred (· in s)
          Equiv.Set.sumDiffSubset (hs.linearIndepOn_id.subset_extend _)

/--
theorem `subset_extend` / 定理 `subset_extend`

English:
theorem subset_extend
  given: {s : Set V} (hs : LinearIndepOn K id s)
  statement: s subseteq hs.extend (Set.subset_univ _)
  proof: hs.subset_extend _

中文:
定理 subset_extend
  条件: {s : Set V} (hs : LinearIndepOn K id s)
  结论: s subseteq hs.extend (Set.subset_univ _)
  证明: hs.subset_extend _

Depends on / 依赖: hs.subset_extend, subset_extend
-/
theorem subset_extend {s : Set V} (hs : LinearIndepOn K id s) : s subseteq hs.extend (Set.subset_univ _) :=
  hs.subset_extend _

/--
Definition of `extendLe` / `extendLe` 的定义

English:
definition extendLe
  signature: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  body: Basis.mk
    ((hs.linearIndepOn_extend _).linearIndependent ..)
    (le_trans ht <| Submodule.span_le.2 <| by simpa using hs.subset_span_extend hst)

中文:
定义 extendLe
  签名: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  定义体: Basis.mk
    ((hs.linearIndepOn_extend _).linearIndependent ..)
    (le_trans ht <| Submodule.span_le.2 <| by simpa using hs.subset_span_extend hst)

Depends on / 依赖: Basis.mk, Submodule, Submodule.span_le, hs.linearIndepOn_extend, hs.subset_span_extend, le_trans, linearIndepOn_extend, linearIndependent, span_le, subset_span_extend
-/
noncomputable def extendLe (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t) :
    Basis (hs.extend hst) K V :=
  Basis.mk
    ((hs.linearIndepOn_extend _).linearIndependent ..)
    (le_trans ht <| Submodule.span_le.2 <| by simpa using hs.subset_span_extend hst)

/--
theorem `extendLe_apply_self` / 定理 `extendLe_apply_self`

English:
theorem extendLe_apply_self
  statement: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  proof: Basis.mk_apply _ _ _

@[simp]

中文:
定理 extendLe_apply_self
  结论: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  证明: Basis.mk_apply _ _ _

@[simp]

Depends on / 依赖: Basis.mk_apply, mk_apply
-/
theorem extendLe_apply_self (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
    (x : hs.extend hst) : Basis.extendLe hs hst ht x = x :=
  Basis.mk_apply _ _ _

@[simp]
/--
theorem `coe_extendLe` / 定理 `coe_extendLe`

English:
theorem coe_extendLe
  given: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  proof: funext (extendLe_apply_self hs hst ht)

中文:
定理 coe_extendLe
  条件: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  证明: funext (extendLe_apply_self hs hst ht)

Depends on / 依赖: extendLe_apply_self
-/
theorem coe_extendLe (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t) :
    ⇑(Basis.extendLe hs hst ht) = ((↑) : _ -> _) :=
  funext (extendLe_apply_self hs hst ht)

/--
theorem `range_extendLe` / 定理 `range_extendLe`

English:
theorem range_extendLe
  given: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  proof: by
  rw [coe_extendLe]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

中文:
定理 range_extendLe
  条件: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  证明: by
  rw [coe_extendLe]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, coe_extendLe, ofPred_mem_eq, range_coe_subtype
-/
theorem range_extendLe (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t) :
    range (Basis.extendLe hs hst ht) = hs.extend hst := by
  rw [coe_extendLe]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

/--
theorem `subset_extendLe` / 定理 `subset_extendLe`

English:
theorem subset_extendLe
  given: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  proof: (range_extendLe hs hst ht).symm ▸ hs.subset_extend hst

中文:
定理 subset_extendLe
  条件: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  证明: (range_extendLe hs hst ht).symm ▸ hs.subset_extend hst

Depends on / 依赖: hs.subset_extend, range_extendLe, subset_extend
-/
theorem subset_extendLe (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t) :
    s subseteq range (Basis.extendLe hs hst ht) :=
  (range_extendLe hs hst ht).symm ▸ hs.subset_extend hst

/--
theorem `extendLe_subset` / 定理 `extendLe_subset`

English:
theorem extendLe_subset
  given: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  proof: (range_extendLe hs hst ht).symm ▸ hs.extend_subset hst

中文:
定理 extendLe_subset
  条件: (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t)
  证明: (range_extendLe hs hst ht).symm ▸ hs.extend_subset hst

Depends on / 依赖: extend_subset, hs.extend_subset, range_extendLe
-/
theorem extendLe_subset (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span K t) :
    range (Basis.extendLe hs hst ht) subseteq t :=
  (range_extendLe hs hst ht).symm ▸ hs.extend_subset hst

/--
Definition of `ofSpan` / `ofSpan` 的定义

English:
definition ofSpan
  signature: (hs : ⊤ <= span K s)
  body: extendLe (linearIndependent_empty K V) (empty_subset s) hs

中文:
定义 ofSpan
  签名: (hs : ⊤ <= span K s)
  定义体: extendLe (linearIndependent_empty K V) (empty_subset s) hs

Depends on / 依赖: empty_subset, extendLe, linearIndependent_empty
-/
noncomputable def ofSpan (hs : ⊤ <= span K s) :
    Basis ((linearIndepOn_empty K id).extend (empty_subset s)) K V :=
  extendLe (linearIndependent_empty K V) (empty_subset s) hs

/--
theorem `ofSpan_apply_self` / 定理 `ofSpan_apply_self`

English:
theorem ofSpan_apply_self
  statement: (hs : ⊤ <= span K s)
  proof: extendLe_apply_self (linearIndependent_empty K V) (empty_subset s) hs x

@[simp]

中文:
定理 ofSpan_apply_self
  结论: (hs : ⊤ <= span K s)
  证明: extendLe_apply_self (linearIndependent_empty K V) (empty_subset s) hs x

@[simp]

Depends on / 依赖: empty_subset, extendLe_apply_self, linearIndependent_empty
-/
theorem ofSpan_apply_self (hs : ⊤ <= span K s)
    (x : (linearIndepOn_empty K id).extend (empty_subset s)) :
    Basis.ofSpan hs x = x :=
  extendLe_apply_self (linearIndependent_empty K V) (empty_subset s) hs x

@[simp]
/--
theorem `coe_ofSpan` / 定理 `coe_ofSpan`

English:
theorem coe_ofSpan
  given: (hs : ⊤ <= span K s)
  statement: ⇑(ofSpan hs) = ((↑) : _ -> _)
  proof: funext (ofSpan_apply_self hs)

中文:
定理 coe_ofSpan
  条件: (hs : ⊤ <= span K s)
  结论: ⇑(ofSpan hs) = ((↑) : _ -> _)
  证明: funext (ofSpan_apply_self hs)

Depends on / 依赖: ofSpan_apply_self
-/
theorem coe_ofSpan (hs : ⊤ <= span K s) : ⇑(ofSpan hs) = ((↑) : _ -> _) :=
  funext (ofSpan_apply_self hs)

/--
theorem `range_ofSpan` / 定理 `range_ofSpan`

English:
theorem range_ofSpan
  given: (hs : ⊤ <= span K s)
  proof: by
  rw [coe_ofSpan]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

中文:
定理 range_ofSpan
  条件: (hs : ⊤ <= span K s)
  证明: by
  rw [coe_ofSpan]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, coe_ofSpan, ofPred_mem_eq, range_coe_subtype
-/
theorem range_ofSpan (hs : ⊤ <= span K s) :
    range (ofSpan hs) = (linearIndepOn_empty K id).extend (empty_subset s) := by
  rw [coe_ofSpan]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

/--
theorem `ofSpan_subset` / 定理 `ofSpan_subset`

English:
theorem ofSpan_subset
  given: (hs : ⊤ <= span K s)
  statement: range (ofSpan hs) subseteq s
  proof: extendLe_subset (linearIndependent_empty K V) (empty_subset s) hs

中文:
定理 ofSpan_subset
  条件: (hs : ⊤ <= span K s)
  结论: range (ofSpan hs) subseteq s
  证明: extendLe_subset (linearIndependent_empty K V) (empty_subset s) hs

Depends on / 依赖: empty_subset, extendLe_subset, linearIndependent_empty
-/
theorem ofSpan_subset (hs : ⊤ <= span K s) : range (ofSpan hs) subseteq s :=
  extendLe_subset (linearIndependent_empty K V) (empty_subset s) hs

section

variable (K V)

/--
Definition of `ofVectorSpaceIndex` / `ofVectorSpaceIndex` 的定义

English:
definition ofVectorSpaceIndex
  signature: : Set V
  body: (linearIndepOn_empty K id).extend (subset_univ _)

中文:
定义 ofVectorSpaceIndex
  签名: : Set V
  定义体: (linearIndepOn_empty K id).extend (subset_univ _)

Depends on / 依赖: extend, linearIndepOn_empty, subset_univ
-/
noncomputable def ofVectorSpaceIndex : Set V :=
  (linearIndepOn_empty K id).extend (subset_univ _)

/--
Definition of `ofVectorSpace` / `ofVectorSpace` 的定义

English:
definition ofVectorSpace
  signature: : Basis (ofVectorSpaceIndex K V) K V
  body: Basis.extend (linearIndependent_empty K V)

@[stacks 09FN "Generalized from fields to division rings."]

中文:
定义 ofVectorSpace
  签名: : Basis (ofVectorSpaceIndex K V) K V
  定义体: Basis.extend (linearIndependent_empty K V)

@[stacks 09FN "Generalized from fields to division rings."]

Depends on / 依赖: Basis.extend, extend, linearIndependent_empty
-/
noncomputable def ofVectorSpace : Basis (ofVectorSpaceIndex K V) K V :=
  Basis.extend (linearIndependent_empty K V)

@[stacks 09FN "Generalized from fields to division rings."]
instance (priority := 100) _root_.Module.Free.of_divisionRing : Module.Free K V :=
  Module.Free.of_basis (ofVectorSpace K V)

/--
theorem `ofVectorSpace_apply_self` / 定理 `ofVectorSpace_apply_self`

English:
theorem ofVectorSpace_apply_self
  given: (x : ofVectorSpaceIndex K V)
  statement: ofVectorSpace K V x = x
  proof: by
  unfold ofVectorSpace
  exact Basis.mk_apply _ _ _

@[simp]

中文:
定理 ofVectorSpace_apply_self
  条件: (x : ofVectorSpaceIndex K V)
  结论: ofVectorSpace K V x = x
  证明: by
  unfold ofVectorSpace
  exact Basis.mk_apply _ _ _

@[simp]

Depends on / 依赖: Basis.mk_apply, mk_apply, ofVectorSpace
-/
theorem ofVectorSpace_apply_self (x : ofVectorSpaceIndex K V) : ofVectorSpace K V x = x := by
  unfold ofVectorSpace
  exact Basis.mk_apply _ _ _

@[simp]
/--
theorem `coe_ofVectorSpace` / 定理 `coe_ofVectorSpace`

English:
theorem coe_ofVectorSpace
  statement: ⇑(ofVectorSpace K V) = ((↑) : _ -> _)
  proof: funext fun x => ofVectorSpace_apply_self K V x

中文:
定理 coe_ofVectorSpace
  结论: ⇑(ofVectorSpace K V) = ((↑) : _ -> _)
  证明: funext fun x => ofVectorSpace_apply_self K V x

Depends on / 依赖: ofVectorSpace_apply_self
-/
theorem coe_ofVectorSpace : ⇑(ofVectorSpace K V) = ((↑) : _ -> _) :=
  funext fun x => ofVectorSpace_apply_self K V x

/--
theorem `ofVectorSpaceIndex.linearIndependent` / 定理 `ofVectorSpaceIndex.linearIndependent`

English:
theorem ofVectorSpaceIndex.linearIndependent
  proof: by
  convert! (ofVectorSpace K V).linearIndependent
  ext x
  rw [ofVectorSpace_apply_self]

中文:
定理 ofVectorSpaceIndex.linearIndependent
  证明: by
  convert! (ofVectorSpace K V).linearIndependent
  ext x
  rw [ofVectorSpace_apply_self]

Depends on / 依赖: convert, linearIndependent, ofVectorSpace, ofVectorSpace_apply_self
-/
theorem ofVectorSpaceIndex.linearIndependent :
    LinearIndependent K ((↑) : ofVectorSpaceIndex K V -> V) := by
  convert! (ofVectorSpace K V).linearIndependent
  ext x
  rw [ofVectorSpace_apply_self]

/--
theorem `range_ofVectorSpace` / 定理 `range_ofVectorSpace`

English:
theorem range_ofVectorSpace
  statement: range (ofVectorSpace K V) = ofVectorSpaceIndex K V
  proof: range_extend _

中文:
定理 range_ofVectorSpace
  结论: range (ofVectorSpace K V) = ofVectorSpaceIndex K V
  证明: range_extend _

Depends on / 依赖: range_extend
-/
theorem range_ofVectorSpace : range (ofVectorSpace K V) = ofVectorSpaceIndex K V :=
  range_extend _

/--
theorem `exists_basis` / 定理 `exists_basis`

English:
theorem exists_basis
  statement: exists s : Set V, Nonempty (Basis s K V)
  proof: ⟨ofVectorSpaceIndex K V, ⟨ofVectorSpace K V⟩⟩

中文:
定理 exists_basis
  结论: 存在 s : Set V, Nonempty (Basis s K V)
  证明: ⟨ofVectorSpaceIndex K V, ⟨ofVectorSpace K V⟩⟩

Depends on / 依赖: ofVectorSpace, ofVectorSpaceIndex
-/
theorem exists_basis : exists s : Set V, Nonempty (Basis s K V) :=
  ⟨ofVectorSpaceIndex K V, ⟨ofVectorSpace K V⟩⟩

end

end ExistsBasis

end Module.Basis

open Fintype

variable (K V)

/--
theorem `VectorSpace.card_fintype` / 定理 `VectorSpace.card_fintype`

English:
theorem VectorSpace.card_fintype
  given: [Fintype K] [Fintype V]
  statement: exists n : Nat, card V = card K ^ n
  proof: by
  classical
  exact ⟨card (Basis.ofVectorSpaceIndex K V), Module.card_fintype (Basis.ofVectorSpace K V)⟩

中文:
定理 VectorSpace.card_fintype
  条件: [Fintype K] [Fintype V]
  结论: 存在 n : 自然数, card V = card K ^ n
  证明: by
  classical
  exact ⟨card (Basis.ofVectorSpaceIndex K V), Module.card_fintype (Basis.ofVectorSpace K V)⟩

Depends on / 依赖: Basis.ofVectorSpace, Basis.ofVectorSpaceIndex, Module, Module.card_fintype, card_fintype, classical, ofVectorSpace, ofVectorSpaceIndex
-/
theorem VectorSpace.card_fintype [Fintype K] [Fintype V] : exists n : Nat, card V = card K ^ n := by
  classical
  exact ⟨card (Basis.ofVectorSpaceIndex K V), Module.card_fintype (Basis.ofVectorSpace K V)⟩

section AtomsOfSubmoduleLattice

variable {K V}

/--
theorem `nonzero_span_atom` / 定理 `nonzero_span_atom`

English:
theorem nonzero_span_atom
  given: (v : V) (hv : v != 0)
  statement: IsAtom (span K {v} : Submodule K V)
  proof: by
  constructor
  · rw [Submodule.ne_bot_iff]
    exact ⟨v, ⟨mem_span_singleton_self v, hv⟩⟩
  · intro T hT
    by_contra h
    apply hT.2
    change span K {v} <= T
    simp_rw [span_singleton_le_iff_mem, ← Ne.eq_def, Submodule.ne_bot_iff] at *
    rcases h with ⟨s, ⟨hs, hz⟩⟩
    rcases mem_span_s

中文:
定理 nonzero_span_atom
  条件: (v : V) (hv : v != 0)
  结论: IsAtom (span K {v} : Submodule K V)
  证明: by
  constructor
  · rw [Submodule.ne_bot_iff]
    exact ⟨v, ⟨mem_span_singleton_self v, hv⟩⟩
  · intro T hT
    by_contra h
    apply hT.2
    change span K {v} <= T
    simp_rw [span_singleton_le_iff_mem, ← Ne.eq_def, Submodule.ne_bot_iff] at *
    rcases h with ⟨s, ⟨hs, hz⟩⟩
    rcases mem_span_s

Depends on / 依赖: Ne.eq_def, Submodule, Submodule.ne_bot_iff, T.smul_mem_iff, eq_def, eq_or_ne, mem_span_singleton, mem_span_singleton_self, ne_bot_iff, ne_eq, not_true, simp_rw, smul_mem_iff, span_singleton_le_iff_mem, zero_smul
-/
theorem nonzero_span_atom (v : V) (hv : v != 0) : IsAtom (span K {v} : Submodule K V) := by
  constructor
  · rw [Submodule.ne_bot_iff]
    exact ⟨v, ⟨mem_span_singleton_self v, hv⟩⟩
  · intro T hT
    by_contra h
    apply hT.2
    change span K {v} <= T
    simp_rw [span_singleton_le_iff_mem, ← Ne.eq_def, Submodule.ne_bot_iff] at *
    rcases h with ⟨s, ⟨hs, hz⟩⟩
    rcases mem_span_singleton.1 (hT.1 hs) with ⟨a, rfl⟩
    rcases eq_or_ne a 0 with rfl | h
    · simp only [zero_smul, ne_eq, not_true] at hz
    · rwa [T.smul_mem_iff h] at hs

/--
theorem `atom_iff_nonzero_span` / 定理 `atom_iff_nonzero_span`

English:
theorem atom_iff_nonzero_span
  given: (W : Submodule K V)
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hbot, h⟩ := h
    rcases (Submodule.ne_bot_iff W).1 hbot with ⟨v, ⟨hW, hv⟩⟩
    refine ⟨v, ⟨hv, ?_⟩⟩
    by_contra heq
    specialize h (span K {v})
    rw [span_singleton_eq_bot]; rw [lt_iff_le_and_ne] at h
    exact hv (h ⟨(span_singleton_le_iff_m

中文:
定理 atom_iff_nonzero_span
  条件: (W : Submodule K V)
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hbot, h⟩ := h
    rcases (Submodule.ne_bot_iff W).1 hbot with ⟨v, ⟨hW, hv⟩⟩
    refine ⟨v, ⟨hv, ?_⟩⟩
    by_contra heq
    specialize h (span K {v})
    rw [span_singleton_eq_bot]; rw [lt_iff_le_and_ne] at h
    exact hv (h ⟨(span_singleton_le_iff_m

Depends on / 依赖: Ne.symm, Submodule, Submodule.ne_bot_iff, lt_iff_le_and_ne, ne_bot_iff, nonzero_span_atom, span_singleton_eq_bot, span_singleton_le_iff_mem, specialize
-/
theorem atom_iff_nonzero_span (W : Submodule K V) :
    IsAtom W ↔ exists v != 0, W = span K {v} := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hbot, h⟩ := h
    rcases (Submodule.ne_bot_iff W).1 hbot with ⟨v, ⟨hW, hv⟩⟩
    refine ⟨v, ⟨hv, ?_⟩⟩
    by_contra heq
    specialize h (span K {v})
    rw [span_singleton_eq_bot]; rw [lt_iff_le_and_ne] at h
    exact hv (h ⟨(span_singleton_le_iff_mem v W).2 hW, Ne.symm heq⟩)
  · rcases h with ⟨v, ⟨hv, rfl⟩⟩
    exact nonzero_span_atom v hv

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsAtomistic (Submodule K V)
  body: CompleteLattice.isAtomistic_iff.2 fun W => by
    refine ⟨_, submodule_eq_sSup_le_nonzero_spans W, ?_⟩
    rintro _ ⟨w, ⟨_, ⟨hw, rfl⟩⟩⟩
    exact nonzero_span_atom w hw

中文:
实例 :
  签名: IsAtomistic (Submodule K V)
  定义体: CompleteLattice.isAtomistic_iff.2 fun W => by
    refine ⟨_, submodule_eq_sSup_le_nonzero_spans W, ?_⟩
    rintro _ ⟨w, ⟨_, ⟨hw, rfl⟩⟩⟩
    exact nonzero_span_atom w hw

Depends on / 依赖: CompleteLattice, CompleteLattice.isAtomistic_iff, isAtomistic_iff, nonzero_span_atom, submodule_eq_sSup_le_nonzero_spans
-/
instance : IsAtomistic (Submodule K V) :=
  CompleteLattice.isAtomistic_iff.2 fun W => by
    refine ⟨_, submodule_eq_sSup_le_nonzero_spans W, ?_⟩
    rintro _ ⟨w, ⟨_, ⟨hw, rfl⟩⟩⟩
    exact nonzero_span_atom w hw

end AtomsOfSubmoduleLattice

variable {K V}

/--
theorem `LinearMap.exists_leftInverse_of_injective` / 定理 `LinearMap.exists_leftInverse_of_injective`

English:
theorem LinearMap.exists_leftInverse_of_injective
  given: (f : V ->ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥)
  proof: by
  let B := Basis.ofVectorSpaceIndex K V
  let hB := Basis.ofVectorSpace K V
  have hB₀ : _ := hB.linearIndependent.linearIndepOn_id
  have : LinearIndepOn K _root_.id (f '' B) := by
    have h₁ : LinearIndepOn K _root_.id (f '' Set.range (Basis.ofVectorSpace K V)) :=
      LinearIndepOn.image (f 

中文:
定理 LinearMap.exists_leftInverse_of_injective
  条件: (f : V ->ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥)
  证明: by
  let B := Basis.ofVectorSpaceIndex K V
  let hB := Basis.ofVectorSpace K V
  have hB₀ : _ := hB.linearIndependent.linearIndepOn_id
  have : LinearIndepOn K _root_.id (f '' B) := by
    have h₁ : LinearIndepOn K _root_.id (f '' Set.range (Basis.ofVectorSpace K V)) :=
      LinearIndepOn.image (f 

Depends on / 依赖: Basis.extend, Basis.ofVectorSpace, Basis.ofVectorSpaceIndex, Basis.range_ofVectorSpace, Disjoint, Inhabi, LinearIndepOn, LinearIndepOn.image, Set.range, _root_, _root_.id, extend, hB.linearIndependent.linearIndepOn_id, hf_inj, linearIndepOn_id, linearIndependent, ofVectorSpace, ofVectorSpaceIndex, range_ofVectorSpace, subset_extend
-/
theorem LinearMap.exists_leftInverse_of_injective (f : V ->ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) :
    exists g : V' ->ₗ[K] V, g.comp f = LinearMap.id := by
  let B := Basis.ofVectorSpaceIndex K V
  let hB := Basis.ofVectorSpace K V
  have hB₀ : _ := hB.linearIndependent.linearIndepOn_id
  have : LinearIndepOn K _root_.id (f '' B) := by
    have h₁ : LinearIndepOn K _root_.id (f '' Set.range (Basis.ofVectorSpace K V)) :=
      LinearIndepOn.image (f := f) hB₀ (show Disjoint _ _ by simp [hf_inj])
    rwa [Basis.range_ofVectorSpace K V] at h₁
  let C := this.extend (subset_univ _)
  have BC := this.subset_extend (subset_univ _)
  let hC := Basis.extend this
  have Vinh : Inhabited V := ⟨0⟩
  refine ⟨(hC.constr Nat : _ -> _) (C.domRestrict (invFun f)), hB.ext fun b => ?_⟩
  rw [image_subset_iff] at BC
  have fb_eq : f b = hC ⟨f b, BC b.2⟩ := by
    change f b = Basis.extend this _
    simp_rw [Basis.extend_apply_self]
  dsimp
  rw [Basis.ofVectorSpace_apply_self]; rw [fb_eq]; rw [hC.constr_basis]
  exact leftInverse_invFun (LinearMap.ker_eq_bot.1 hf_inj) _

/-- The left inverse of `f : E →ₗ[𝕜] F`.

If `f` is not injective, then we use the junk value `0`. -/
noncomputable
/--
Definition of `LinearMap.leftInverse` / `LinearMap.leftInverse` 的定义

English:
definition LinearMap.leftInverse
  signature: (f : V ->ₗ[K] V')
  body: if h_inj : LinearMap.ker f = ⊥ then
  (f.exists_leftInverse_of_injective h_inj).choose
  else 0

中文:
定义 LinearMap.leftInverse
  签名: (f : V ->ₗ[K] V')
  定义体: if h_inj : LinearMap.ker f = ⊥ then
  (f.exists_leftInverse_of_injective h_inj).choose
  else 0

Depends on / 依赖: LinearMap, LinearMap.ker, exists_leftInverse_of_injective, f.exists_leftInverse_of_injective, h_inj
-/
def LinearMap.leftInverse (f : V ->ₗ[K] V') : V' ->ₗ[K] V :=
  if h_inj : LinearMap.ker f = ⊥ then
  (f.exists_leftInverse_of_injective h_inj).choose
  else 0

/--
theorem `LinearMap.leftInverse_comp_of_inj` / 定理 `LinearMap.leftInverse_comp_of_inj`

English:
theorem LinearMap.leftInverse_comp_of_inj
  given: {f : V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥)
  proof: by
  simpa [leftInverse, h_inj] using (f.exists_leftInverse_of_injective h_inj).choose_spec

中文:
定理 LinearMap.leftInverse_comp_of_inj
  条件: {f : V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥)
  证明: by
  simpa [leftInverse, h_inj] using (f.exists_leftInverse_of_injective h_inj).choose_spec

Depends on / 依赖: choose_spec, exists_leftInverse_of_injective, f.exists_leftInverse_of_injective, h_inj, leftInverse
-/
theorem LinearMap.leftInverse_comp_of_inj {f : V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) :
    f.leftInverse ∘ₗ f = LinearMap.id := by
  simpa [leftInverse, h_inj] using (f.exists_leftInverse_of_injective h_inj).choose_spec

/--
theorem `LinearMap.leftInverse_apply_of_inj` / 定理 `LinearMap.leftInverse_apply_of_inj`

English:
theorem LinearMap.leftInverse_apply_of_inj
  given: {f : V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) (x : V)
  proof: LinearMap.ext_iff.mp (f.leftInverse_comp_of_inj h_inj) x

中文:
定理 LinearMap.leftInverse_apply_of_inj
  条件: {f : V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) (x : V)
  证明: LinearMap.ext_iff.mp (f.leftInverse_comp_of_inj h_inj) x

Depends on / 依赖: LinearMap, LinearMap.ext_iff.mp, ext_iff, f.leftInverse_comp_of_inj, h_inj, leftInverse_comp_of_inj
-/
theorem LinearMap.leftInverse_apply_of_inj {f : V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) (x : V) :
    f.leftInverse (f x) = x :=
  LinearMap.ext_iff.mp (f.leftInverse_comp_of_inj h_inj) x

/--
theorem `Submodule.exists_isCompl` / 定理 `Submodule.exists_isCompl`

English:
theorem Submodule.exists_isCompl
  given: (p : Submodule K V)
  statement: exists q : Submodule K V, IsCompl p q
  proof: ⟨LinearMap.ker p.subtype.leftInverse,
LinearMap.isCompl_of_proj LinearMap.leftInverse_apply_of_inj p.ker_subtype⟩

中文:
定理 Submodule.exists_isCompl
  条件: (p : Submodule K V)
  结论: 存在 q : Submodule K V, IsCompl p q
  证明: ⟨LinearMap.ker p.subtype.leftInverse,
LinearMap.isCompl_of_proj LinearMap.leftInverse_apply_of_inj p.ker_subtype⟩

Depends on / 依赖: LinearMap, LinearMap.isCompl_of_proj, LinearMap.ker, LinearMap.leftInverse_apply_of_inj, isCompl_of_proj, ker_subtype, leftInverse, leftInverse_apply_of_inj, p.ker_subtype, p.subtype.leftInverse, subtype
-/
theorem Submodule.exists_isCompl (p : Submodule K V) : exists q : Submodule K V, IsCompl p q :=
  ⟨LinearMap.ker p.subtype.leftInverse,
LinearMap.isCompl_of_proj LinearMap.leftInverse_apply_of_inj p.ker_subtype⟩

/--
Instance `Submodule.complementedLattice` / 实例 `Submodule.complementedLattice`

English:
instance Submodule.complementedLattice
  signature: : ComplementedLattice (Submodule K V)
  body: ⟨Submodule.exists_isCompl⟩

中文:
实例 Submodule.complementedLattice
  签名: : ComplementedLattice (Submodule K V)
  定义体: ⟨Submodule.exists_isCompl⟩

Depends on / 依赖: Submodule, Submodule.exists_isCompl, exists_isCompl
-/
instance Submodule.complementedLattice : ComplementedLattice (Submodule K V) :=
  ⟨Submodule.exists_isCompl⟩

/--
theorem `LinearMap.exists_extend` / 定理 `LinearMap.exists_extend`

English:
theorem LinearMap.exists_extend
  given: {p : Submodule K V} (f : p ->ₗ[K] V')
  proof: let ⟨g, hg⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨f.comp g, by rw [LinearMap.comp_assoc, hg, f.comp_id]⟩

中文:
定理 LinearMap.exists_extend
  条件: {p : Submodule K V} (f : p ->ₗ[K] V')
  证明: let ⟨g, hg⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨f.comp g, by rw [LinearMap.comp_assoc, hg, f.comp_id]⟩

Depends on / 依赖: LinearMap, LinearMap.comp_assoc, comp_assoc, comp_id, exists_leftInverse_of_injective, f.comp, f.comp_id, ker_subtype, p.ker_subtype, p.subtype.exists_leftInverse_of_injective, subtype
-/
theorem LinearMap.exists_extend {p : Submodule K V} (f : p ->ₗ[K] V') :
    exists g : V ->ₗ[K] V', g.comp p.subtype = f :=
  let ⟨g, hg⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨f.comp g, by rw [LinearMap.comp_assoc, hg, f.comp_id]⟩

/--
theorem `LinearMap.exists_extend_of_notMem` / 定理 `LinearMap.exists_extend_of_notMem`

English:
theorem LinearMap.exists_extend_of_notMem
  statement: {p : Submodule K V} {v : V} (f : p ->ₗ[K] V')
  proof: by
  rcases (LinearPMap.supSpanSingleton ⟨p, f⟩ v y hv).toFun.exists_extend with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · ext x
    have := LinearPMap.supSpanSingleton_apply_mk_of_mem ⟨p, f⟩ y hv x.2
    simpa using! congr($hg _).trans this
  · have := LinearPMap.supSpanSingleton_apply_self ⟨p, f⟩ y hv
    

中文:
定理 LinearMap.exists_extend_of_notMem
  结论: {p : Submodule K V} {v : V} (f : p ->ₗ[K] V')
  证明: by
  rcases (LinearPMap.supSpanSingleton ⟨p, f⟩ v y hv).toFun.exists_extend with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · ext x
    have := LinearPMap.supSpanSingleton_apply_mk_of_mem ⟨p, f⟩ y hv x.2
    simpa using! congr($hg _).trans this
  · have := LinearPMap.supSpanSingleton_apply_self ⟨p, f⟩ y hv
    

Depends on / 依赖: LinearPMap, LinearPMap.supSpanSingleton, LinearPMap.supSpanSingleton_apply_mk_of_mem, LinearPMap.supSpanSingleton_apply_self, exists_extend, supSpanSingleton, supSpanSingleton_apply_mk_of_mem, supSpanSingleton_apply_self, toFun.exists_extend
-/
theorem LinearMap.exists_extend_of_notMem {p : Submodule K V} {v : V} (f : p ->ₗ[K] V')
    (hv : v ∉ p) (y : V') : exists g : V ->ₗ[K] V', g.comp p.subtype = f ∧ g v = y := by
  rcases (LinearPMap.supSpanSingleton ⟨p, f⟩ v y hv).toFun.exists_extend with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · ext x
    have := LinearPMap.supSpanSingleton_apply_mk_of_mem ⟨p, f⟩ y hv x.2
    simpa using! congr($hg _).trans this
  · have := LinearPMap.supSpanSingleton_apply_self ⟨p, f⟩ y hv
    simpa using! congr($hg _).trans this

open Submodule LinearMap

/--
theorem `Submodule.exists_le_ker_of_notMem` / 定理 `Submodule.exists_le_ker_of_notMem`

English:
theorem Submodule.exists_le_ker_of_notMem
  given: {p : Submodule K V} {v : V} (hv : v ∉ p)
  proof: by
  rcases LinearMap.exists_extend_of_notMem (0 : p ->ₗ[K] K) hv 1 with ⟨f, hpf, hfv⟩
  refine ⟨f, by simp [hfv], fun x hx => ?_⟩
  simpa using congr($hpf ⟨x, hx⟩)

中文:
定理 Submodule.exists_le_ker_of_notMem
  条件: {p : Submodule K V} {v : V} (hv : v ∉ p)
  证明: by
  rcases LinearMap.exists_extend_of_notMem (0 : p ->ₗ[K] K) hv 1 with ⟨f, hpf, hfv⟩
  refine ⟨f, by simp [hfv], fun x hx => ?_⟩
  simpa using congr($hpf ⟨x, hx⟩)

Depends on / 依赖: LinearMap, LinearMap.exists_extend_of_notMem, exists_extend_of_notMem
-/
theorem Submodule.exists_le_ker_of_notMem {p : Submodule K V} {v : V} (hv : v ∉ p) :
    exists f : V ->ₗ[K] K, f v != 0 ∧ p <= ker f := by
  rcases LinearMap.exists_extend_of_notMem (0 : p ->ₗ[K] K) hv 1 with ⟨f, hpf, hfv⟩
  refine ⟨f, by simp [hfv], fun x hx => ?_⟩
  simpa using congr($hpf ⟨x, hx⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: V] [Nontrivial V'] : Nontrivial (V ->ₗ[K] V')
  body: by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : V')
  have : v ∉ (⊥ : Submodule K V) := by simp only [mem_bot, hv, not_false_eq_true]
  obtain ⟨g, _, hg⟩ := LinearMap.exists_extend_of_notMem (K := K) 0 this w
  exact ⟨g, 0, DFunLike.ne_iff.mpr ⟨v, by simp_all⟩⟩

中文:
实例 [Nontrivial
  签名: V] [Nontrivial V'] : Nontrivial (V ->ₗ[K] V')
  定义体: by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : V')
  have : v ∉ (⊥ : Submodule K V) := by simp only [mem_bot, hv, not_false_eq_true]
  obtain ⟨g, _, hg⟩ := LinearMap.exists_extend_of_notMem (K := K) 0 this w
  exact ⟨g, 0, DFunLike.ne_iff.mpr ⟨v, by simp_all⟩⟩

Depends on / 依赖: DFunLike, DFunLike.ne_iff.mpr, LinearMap, LinearMap.exists_extend_of_notMem, Submodule, exists_extend_of_notMem, exists_ne, mem_bot, ne_iff, not_false_eq_true
-/
instance [Nontrivial V] [Nontrivial V'] : Nontrivial (V ->ₗ[K] V') := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : V')
  have : v ∉ (⊥ : Submodule K V) := by simp only [mem_bot, hv, not_false_eq_true]
  obtain ⟨g, _, hg⟩ := LinearMap.exists_extend_of_notMem (K := K) 0 this w
  exact ⟨g, 0, DFunLike.ne_iff.mpr ⟨v, by simp_all⟩⟩

/--
theorem `Submodule.exists_le_ker_of_lt_top` / 定理 `Submodule.exists_le_ker_of_lt_top`

English:
theorem Submodule.exists_le_ker_of_lt_top
  given: (p : Submodule K V) (hp : p < ⊤)
  proof: by
  rcases SetLike.exists_of_lt hp with ⟨v, -, hpv⟩
  rcases exists_le_ker_of_notMem hpv with ⟨f, hfv, hpf⟩
  exact ⟨f, ne_of_apply_ne (· v) hfv, hpf⟩

中文:
定理 Submodule.exists_le_ker_of_lt_top
  条件: (p : Submodule K V) (hp : p < ⊤)
  证明: by
  rcases SetLike.exists_of_lt hp with ⟨v, -, hpv⟩
  rcases exists_le_ker_of_notMem hpv with ⟨f, hfv, hpf⟩
  exact ⟨f, ne_of_apply_ne (· v) hfv, hpf⟩

Depends on / 依赖: SetLike, SetLike.exists_of_lt, exists_le_ker_of_notMem, exists_of_lt, ne_of_apply_ne
-/
theorem Submodule.exists_le_ker_of_lt_top (p : Submodule K V) (hp : p < ⊤) :
    exists (f : V ->ₗ[K] K), f != 0 ∧ p <= ker f := by
  rcases SetLike.exists_of_lt hp with ⟨v, -, hpv⟩
  rcases exists_le_ker_of_notMem hpv with ⟨f, hfv, hpf⟩
  exact ⟨f, ne_of_apply_ne (· v) hfv, hpf⟩

/--
theorem `quotient_prod_linearEquiv` / 定理 `quotient_prod_linearEquiv`

English:
theorem quotient_prod_linearEquiv
  given: (p : Submodule K V)
  statement: Nonempty (((V ⧸ p) × p) ≃ₗ[K] V)
  proof: let ⟨q, hq⟩ := p.exists_isCompl
Nonempty.intro
    ((quotientEquivOfIsCompl p q hq).prodCongr (LinearEquiv.refl _ _)).trans
      (prodEquivOfIsCompl q p hq.symm)

中文:
定理 quotient_prod_linearEquiv
  条件: (p : Submodule K V)
  结论: Nonempty (((V ⧸ p) × p) ≃ₗ[K] V)
  证明: let ⟨q, hq⟩ := p.exists_isCompl
Nonempty.intro
    ((quotientEquivOfIsCompl p q hq).prodCongr (LinearEquiv.refl _ _)).trans
      (prodEquivOfIsCompl q p hq.symm)

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, Nonempty, Nonempty.intro, exists_isCompl, hq.symm, p.exists_isCompl, prodCongr, prodEquivOfIsCompl, quotientEquivOfIsCompl
-/
theorem quotient_prod_linearEquiv (p : Submodule K V) : Nonempty (((V ⧸ p) × p) ≃ₗ[K] V) :=
  let ⟨q, hq⟩ := p.exists_isCompl
Nonempty.intro
    ((quotientEquivOfIsCompl p q hq).prodCongr (LinearEquiv.refl _ _)).trans
      (prodEquivOfIsCompl q p hq.symm)

end DivisionRing

section Field

open Submodule LinearMap Module

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {f : V ->ₗ[K] K} {v : V}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_basis_of_pairing_ne_zero` / 定理 `exists_basis_of_pairing_ne_zero`

English:
theorem exists_basis_of_pairing_ne_zero
  proof: by
  set b₁ := Basis.ofVectorSpace K (ker f)
  set s : Set V := (ker f).subtype '' Set.range b₁
  have hs : span K s = ker f := by
    simp only [s, span_image]
    simp
  set n := insert v s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.im

中文:
定理 exists_basis_of_pairing_ne_zero
  证明: by
  set b₁ := Basis.ofVectorSpace K (ker f)
  set s : Set V := (ker f).subtype '' Set.range b₁
  have hs : span K s = ker f := by
    simp only [s, span_image]
    simp
  set n := insert v s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.im

Depends on / 依赖: Basis.ofVectorSpace, LinearIndepOn, LinearIndepOn.id_insert, LinearIndepOn.image, Set.range, _root_, _root_.id, id_insert, insert, linearIndepOn_id, linearIndependent, linearIndependent.linearIndepOn_id, map_add, map_smul, mem_ker, mem_span_insert, ofVectorSpace, smul_eq_mul, span_image, subtype
-/
theorem exists_basis_of_pairing_ne_zero
    (hfv : f v != 0) :
    exists (n : Set V) (b : Module.Basis n K V) (i : n),
      v = b i ∧ f = (f v) • b.coord i := by
  set b₁ := Basis.ofVectorSpace K (ker f)
  set s : Set V := (ker f).subtype '' Set.range b₁
  have hs : span K s = ker f := by
    simp only [s, span_image]
    simp
  set n := insert v s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.image
      · exact b₁.linearIndependent.linearIndepOn_id
      · simp
    · simp [hs, hfv]
  have H₂ : ⊤ <= span K n := by
    rintro x -
    simp only [n, mem_span_insert']
    use -f x / f v
    simp only [hs, mem_ker, map_add, map_smul, smul_eq_mul]
    field
  set b := Basis.mk H₁ (by simpa using H₂)
  set i : n := ⟨v, s.mem_insert v⟩
  have hi : b i = v := by simp [b, i]
  refine ⟨n, b, i, by simp [b, i], ?_⟩
  rw [← hi]
  apply b.ext
  intro j
  by_cases h : i = j
  · simp [h]
  · suffices f (b j) = 0 by
      simp [Finsupp.single_eq_of_ne h, this]
    rw [← mem_ker]; rw [← hs]; rw [Basis.coe_mk]
    apply subset_span
    apply Or.resolve_left (Set.mem_insert_iff.mpr j.prop)
    simp [← hi, b, Subtype.coe_inj, Ne.symm h]

/--
theorem `exists_basis_of_pairing_eq_zero` / 定理 `exists_basis_of_pairing_eq_zero`

English:
theorem exists_basis_of_pairing_eq_zero
  proof: by
  lift v to ker f using hfv
  have : LinearIndepOn K _root_.id {v} := by simpa using hv
  set b₁ : Basis _ K (ker f) := .extend this
  obtain ⟨w, hw⟩ : exists w, f w = 1 := by
    simp only [ne_eq, DFunLike.ext_iff, not_forall] at hf
    rcases hf with ⟨w, hw⟩
    use (f w)⁻¹ • w
    simp_all
  s

中文:
定理 exists_basis_of_pairing_eq_zero
  证明: by
  lift v to ker f using hfv
  have : LinearIndepOn K _root_.id {v} := by simpa using hv
  set b₁ : Basis _ K (ker f) := .extend this
  obtain ⟨w, hw⟩ : exists w, f w = 1 := by
    simp only [ne_eq, DFunLike.ext_iff, not_forall] at hf
    rcases hf with ⟨w, hw⟩
    use (f w)⁻¹ • w
    simp_all
  s

Depends on / 依赖: DFunLike, DFunLike.ext_iff, LinearIndepOn, Set.range, _root_, _root_.id, ext_iff, extend, insert, ne_eq, not_forall, span_image, subset_extend, subtype, this.subset_extend
-/
theorem exists_basis_of_pairing_eq_zero
    (hfv : f v = 0) (hf : f != 0) (hv : v != 0) :
    exists (n : Set V) (b : Basis n K V) (i j : n),
      i != j ∧ v = b i ∧ f = b.coord j := by
  lift v to ker f using hfv
  have : LinearIndepOn K _root_.id {v} := by simpa using hv
  set b₁ : Basis _ K (ker f) := .extend this
  obtain ⟨w, hw⟩ : exists w, f w = 1 := by
    simp only [ne_eq, DFunLike.ext_iff, not_forall] at hf
    rcases hf with ⟨w, hw⟩
    use (f w)⁻¹ • w
    simp_all
  set s : Set V := (ker f).subtype '' Set.range b₁
  have hs : span K s = ker f := by
    simp only [s, span_image]
    simp
  have hvs : ↑v in s := by
    refine ⟨v, ?_, by simp⟩
    simp [b₁, this.subset_extend _ _]
  set n := insert w s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.image
      · exact b₁.linearIndependent.linearIndepOn_id
      · simp
    · simp [hs, hw]
  have H₂ : ⊤ <= span K n := by
    rintro x -
    simp only [n, mem_span_insert']
    use -f x
    simp [hs, hw]
  set b := Basis.mk H₁ (by simpa using H₂)
  refine ⟨n, b, ⟨v, by simp [n, hvs]⟩, ⟨w, by simp [n]⟩, ?_, by simp [b], ?_⟩
  · apply_fun (f ∘ (↑))
    simp [hw]
  · apply b.ext
    intro i
    rw [Basis.coord_apply]; rw [Basis.repr_self]
    simp only [b]
    rcases i with ⟨x, rfl | ⟨x, hx, rfl⟩⟩
    · simp [hw]
    · suffices x != w by simp [this]
      apply_fun f
      simp [hw]

end Field
