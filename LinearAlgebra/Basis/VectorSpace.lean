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
variable {v : ι → V} {s t : Set V} {x y z : V}

open Submodule

namespace Module.Basis

section ExistsBasis

/-- If `s` is a linear independent set of vectors, we can extend it to a basis. -/
/-
**Module.Basis.extend** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：extend (hs : LinearIndepOn K id s) : Basis (hs.extend (subset_univ s)) K V
参数：hs : LinearIndepOn K id s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ

--- 原说明 ---
If `s` is a linear independent set of vectors, we can extend it to a basis.
-/
noncomputable def extend (hs : LinearIndepOn K id s) :
    Basis (hs.extend (subset_univ s)) K V :=
  Basis.mk
    (hs.linearIndepOn_extend _).linearIndependent_restrict
    (SetLike.coe_subset_coe.mp <| by simpa using hs.subset_span_extend (subset_univ s))
/-
**Module.Basis.extend_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：extend_apply_self (hs : LinearIndepOn K id s) (x : hs.extend _) : Basis.ex
tend hs x = x
参数：hs : LinearIndepOn K id s；x : hs.extend _。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Module.Basis.mk_apply`：mk_apply (i : ι) : Basis.mk hli hsp i = v i
-/
theorem extend_apply_self (hs : LinearIndepOn K id s) (x : hs.extend _) : Basis.extend hs x = x :=
  Basis.mk_apply _ _ _

@[simp]
/-
**Module.Basis.coe_extend** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_extend (hs : LinearIndepOn K id s) : ⇑(Basis.extend hs) = ((↑) : _ -> 
_)
参数：hs : LinearIndepOn K id s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Module.Basis.extend_apply_self`：extend_apply_self (hs : LinearIndepOn K 
id s) (x : hs.extend _) : Basis.extend hs x = x
-/
theorem coe_extend (hs : LinearIndepOn K id s) : ⇑(Basis.extend hs) = ((↑) : _ → _) :=
  funext (extend_apply_self hs)
/-
**Module.Basis.range_extend** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：range_extend (hs : LinearIndepOn K id s) : range (Basis.extend hs) = hs.ex
tend (subset_univ _)
参数：hs : LinearIndepOn K id s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coe_extend`：coe_extend (hs : LinearIndepOn K id s) : ⇑(Basi
s.extend hs) = ((↑) : _ -> _)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
-/
theorem range_extend (hs : LinearIndepOn K id s) :
    range (Basis.extend hs) = hs.extend (subset_univ _) := by
  rw [coe_extend, Subtype.range_coe_subtype, ofPred_mem_eq]

/-- Auxiliary definition: the index for the new basis vectors in `Basis.sumExtend`.

The specific value of this definition should be considered an implementation detail. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**Module.Basis.sumExtendIndex** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：sumExtendIndex (hs : LinearIndependent K v) : Set V
参数：hs : LinearIndependent K v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def sumExtendIndex (hs : LinearIndependent K v) : Set V :=
  LinearIndepOn.extend hs.linearIndepOn_id (subset_univ _) \ range v

/-- If `v` is a linear independent family of vectors, extend it to a basis indexed by a sum type. -/
/-
**Module.Basis.sumExtend** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：sumExtend (hs : LinearIndependent K v) : Basis (ι oplus sumExtendIndex hs)
 K V
参数：hs : LinearIndependent K v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
If `v` is a linear independent family of vectors, extend it to a basis indexed b
y a sum type.
-/
noncomputable def sumExtend (hs : LinearIndependent K v) : Basis (ι ⊕ sumExtendIndex hs) K V :=
  let s := Set.range v
  let e : ι ≃ s := Equiv.ofInjective v hs.injective
  let b := hs.linearIndepOn_id.extend (subset_univ (Set.range v))
  (Basis.extend hs.linearIndepOn_id).reindex <|
    Equiv.symm <|
      calc
        ι ⊕ (b \ s : Set V) ≃ s ⊕ (b \ s : Set V) := Equiv.sumCongr e (Equiv.refl _)
        _ ≃ b :=
          haveI := Classical.decPred (· ∈ s)
          Equiv.Set.sumDiffSubset (hs.linearIndepOn_id.subset_extend _)
/-
**Module.Basis.subset_extend** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：subset_extend {s : Set V} (hs : LinearIndepOn K id s) : s subseteq hs.exte
nd (Set.subset_univ _)
参数：hs : LinearIndepOn K id s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.subset_extend`：LinearIndepOn.subset_extend (hs : LinearInd
epOn K v s) (hst : s subseteq t) : s subseteq hs.extend hst
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem subset_extend {s : Set V} (hs : LinearIndepOn K id s) : s ⊆ hs.extend (Set.subset_univ _) :=
  hs.subset_extend _

/-- If `s` is a family of linearly independent vectors contained in a set `t` spanning `V`,
then one can get a basis of `V` containing `s` and contained in `t`. -/
/-
**Module.Basis.extendLe** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：extendLe (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= span 
K t) : Basis (hs.extend hst) K V
参数：hs : LinearIndepOn K id s；hst : s subseteq t；ht : ⊤ <= span K t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a family of linearly independent vectors contained in a set `t` spanni
ng `V`,
then one can get a basis of `V` containing `s` and contained in `t`.
-/
noncomputable def extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    Basis (hs.extend hst) K V :=
  Basis.mk
    ((hs.linearIndepOn_extend _).linearIndependent ..)
    (le_trans ht <| Submodule.span_le.2 <| by simpa using hs.subset_span_extend hst)
/-
**Module.Basis.extendLe_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：extendLe_apply_self (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht :
 ⊤ <= span K t) (x : hs.extend hst) : Basis.extendLe hs hst ht x = x
参数：hs : LinearIndepOn K id s；hst : s subseteq t；ht : ⊤ <= span K t；x : hs.extend
 hst。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.mk_apply`：mk_apply (i : ι) : Basis.mk hli hsp i = v i
-/
theorem extendLe_apply_self (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t)
    (x : hs.extend hst) : Basis.extendLe hs hst ht x = x :=
  Basis.mk_apply _ _ _

@[simp]
/-
**Module.Basis.coe_extendLe** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_extendLe (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <= s
pan K t) : ⇑(Basis.extendLe hs hst ht) = ((↑) : _ -> _)
参数：hs : LinearIndepOn K id s；hst : s subseteq t；ht : ⊤ <= span K t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.extendLe_apply_self`：extendLe_apply_self (hs : LinearIndepO
n K id s) (hst : s subseteq t) (ht : ⊤ <= span K t) (x : hs.extend hst) : Basis.
extendLe hs hst ht x =…
-/
theorem coe_extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    ⇑(Basis.extendLe hs hst ht) = ((↑) : _ → _) :=
  funext (extendLe_apply_self hs hst ht)
/-
**Module.Basis.range_extendLe** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：range_extendLe (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <=
 span K t) : range (Basis.extendLe hs hst ht) = hs.extend hst
参数：hs : LinearIndepOn K id s；hst : s subseteq t；ht : ⊤ <= span K t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coe_extendLe`：coe_extendLe (hs : LinearIndepOn K id s) (hst
 : s subseteq t) (ht : ⊤ <= span K t) : ⇑(Basis.extendLe hs hst ht) = ((↑) : _ -
> _)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
-/
theorem range_extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    range (Basis.extendLe hs hst ht) = hs.extend hst := by
  rw [coe_extendLe, Subtype.range_coe_subtype, ofPred_mem_eq]
/-
**Module.Basis.subset_extendLe** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：subset_extendLe (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <
= span K t) : s subseteq range (Basis.extendLe hs hst ht)
参数：hs : LinearIndepOn K id s；hst : s subseteq t；ht : ⊤ <= span K t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.subset_extend`：LinearIndepOn.subset_extend (hs : LinearInd
epOn K v s) (hst : s subseteq t) : s subseteq hs.extend hst
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.range_extendLe`：range_extendLe (hs : LinearIndepOn K id s) 
(hst : s subseteq t) (ht : ⊤ <= span K t) : range (Basis.extendLe hs hst ht) = h
s.extend hst
-/
theorem subset_extendLe (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    s ⊆ range (Basis.extendLe hs hst ht) :=
  (range_extendLe hs hst ht).symm ▸ hs.subset_extend hst
/-
**Module.Basis.extendLe_subset** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：extendLe_subset (hs : LinearIndepOn K id s) (hst : s subseteq t) (ht : ⊤ <
= span K t) : range (Basis.extendLe hs hst ht) subseteq t
参数：hs : LinearIndepOn K id s；hst : s subseteq t；ht : ⊤ <= span K t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndepOn.extend_subset`：LinearIndepOn.extend_subset (hs : LinearInd
epOn K v s) (hst : s subseteq t) : hs.extend hst subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.range_extendLe`：range_extendLe (hs : LinearIndepOn K id s) 
(hst : s subseteq t) (ht : ⊤ <= span K t) : range (Basis.extendLe hs hst ht) = h
s.extend hst
-/
theorem extendLe_subset (hs : LinearIndepOn K id s) (hst : s ⊆ t) (ht : ⊤ ≤ span K t) :
    range (Basis.extendLe hs hst ht) ⊆ t :=
  (range_extendLe hs hst ht).symm ▸ hs.extend_subset hst

/-- If a set `s` spans the space, this is a basis contained in `s`. -/
/-
**Module.Basis.ofSpan** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：ofSpan (hs : ⊤ <= span K s) : Basis ((linearIndepOn_empty K id).extend (em
pty_subset s)) K V
参数：hs : ⊤ <= span K s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s

--- 原说明 ---
If a set `s` spans the space, this is a basis contained in `s`.
-/
noncomputable def ofSpan (hs : ⊤ ≤ span K s) :
    Basis ((linearIndepOn_empty K id).extend (empty_subset s)) K V :=
  extendLe (linearIndependent_empty K V) (empty_subset s) hs
/-
**Module.Basis.ofSpan_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：ofSpan_apply_self (hs : ⊤ <= span K s) (x : (linearIndepOn_empty K id).ext
end (empty_subset s)) : Basis.ofSpan hs x = x
参数：hs : ⊤ <= span K s；x : (linearIndepOn_empty K id).extend (empty_subset s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndepOn_empty`：linearIndepOn_empty : LinearIndepOn R v ∅
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Module.Basis.extendLe_apply_self`：extendLe_apply_self (hs : LinearIndepO
n K id s) (hst : s subseteq t) (ht : ⊤ <= span K t) (x : hs.extend hst) : Basis.
extendLe hs hst ht x =…
· 使用定理 `linearIndependent_empty`：linearIndependent_empty : LinearIndependent R (
fun x => x : (∅ : Set M) -> M)
-/
theorem ofSpan_apply_self (hs : ⊤ ≤ span K s)
    (x : (linearIndepOn_empty K id).extend (empty_subset s)) :
    Basis.ofSpan hs x = x :=
  extendLe_apply_self (linearIndependent_empty K V) (empty_subset s) hs x

@[simp]
/-
**Module.Basis.coe_ofSpan** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_ofSpan (hs : ⊤ <= span K s) : ⇑(ofSpan hs) = ((↑) : _ -> _)
参数：hs : ⊤ <= span K s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `linearIndepOn_empty`：linearIndepOn_empty : LinearIndepOn R v ∅
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `Module.Basis.ofSpan_apply_self`：ofSpan_apply_self (hs : ⊤ <= span K s) (
x : (linearIndepOn_empty K id).extend (empty_subset s)) : Basis.ofSpan hs x = x
-/
theorem coe_ofSpan (hs : ⊤ ≤ span K s) : ⇑(ofSpan hs) = ((↑) : _ → _) :=
  funext (ofSpan_apply_self hs)
/-
**Module.Basis.range_ofSpan** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：range_ofSpan (hs : ⊤ <= span K s) : range (ofSpan hs) = (linearIndepOn_emp
ty K id).extend (empty_subset s)
参数：hs : ⊤ <= span K s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `linearIndepOn_empty`：linearIndepOn_empty : LinearIndepOn R v ∅
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coe_ofSpan`：coe_ofSpan (hs : ⊤ <= span K s) : ⇑(ofSpan hs) 
= ((↑) : _ -> _)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Set.ofPred_mem_eq`：∀ {α : Type u} {s : Set α}, {x | x ∈ s} = s
-/
theorem range_ofSpan (hs : ⊤ ≤ span K s) :
    range (ofSpan hs) = (linearIndepOn_empty K id).extend (empty_subset s) := by
  rw [coe_ofSpan, Subtype.range_coe_subtype, ofPred_mem_eq]
/-
**Module.Basis.ofSpan_subset** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：ofSpan_subset (hs : ⊤ <= span K s) : range (ofSpan hs) subseteq s
参数：hs : ⊤ <= span K s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.extendLe_subset`：extendLe_subset (hs : LinearIndepOn K id s
) (hst : s subseteq t) (ht : ⊤ <= span K t) : range (Basis.extendLe hs hst ht) s
ubseteq t
· 使用定理 `linearIndependent_empty`：linearIndependent_empty : LinearIndependent R (
fun x => x : (∅ : Set M) -> M)
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
-/
theorem ofSpan_subset (hs : ⊤ ≤ span K s) : range (ofSpan hs) ⊆ s :=
  extendLe_subset (linearIndependent_empty K V) (empty_subset s) hs

section

variable (K V)

/-- A set used to index `Basis.ofVectorSpace`. -/
/-
**Module.Basis.ofVectorSpaceIndex** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：ofVectorSpaceIndex : Set V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set used to index `Basis.ofVectorSpace`.
-/
noncomputable def ofVectorSpaceIndex : Set V :=
  (linearIndepOn_empty K id).extend (subset_univ _)

/-- Each vector space has a basis. -/
/-
**Module.Basis.ofVectorSpace** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：ofVectorSpace : Basis (ofVectorSpaceIndex K V) K V
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Each vector space has a basis.
-/
noncomputable def ofVectorSpace : Basis (ofVectorSpaceIndex K V) K V :=
  Basis.extend (linearIndependent_empty K V)

@[stacks 09FN "Generalized from fields to division rings."]
/-
**Module.Basis.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Basis`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) _root_.Module.Free.of_divisionRing : Module.Free K V :=
  Module.Free.of_basis (ofVectorSpace K V)
/-
**Module.Basis.ofVectorSpace_apply_self** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`
。
形式化陈述：ofVectorSpace_apply_self (x : ofVectorSpaceIndex K V) : ofVectorSpace K V 
x = x
参数：x : ofVectorSpaceIndex K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.mk_apply`：mk_apply (i : ι) : Basis.mk hli hsp i = v i
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem ofVectorSpace_apply_self (x : ofVectorSpaceIndex K V) : ofVectorSpace K V x = x := by
  unfold ofVectorSpace
  exact Basis.mk_apply _ _ _

@[simp]
/-
**Module.Basis.coe_ofVectorSpace** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：coe_ofVectorSpace : ⇑(ofVectorSpace K V) = ((↑) : _ -> _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.Basis.ofVectorSpace_apply_self`：ofVectorSpace_apply_self (x : ofV
ectorSpaceIndex K V) : ofVectorSpace K V x = x
-/
theorem coe_ofVectorSpace : ⇑(ofVectorSpace K V) = ((↑) : _ → _) :=
  funext fun x => ofVectorSpace_apply_self K V x
/-
**Module.Basis.ofVectorSpaceIndex.linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `M
odule.Basis.ofVectorSpaceIndex`。
形式化陈述：∀ (K : Type u_3) (V : Type u_4) [inst : DivisionRing K] [inst_1 : AddCommG
roup V] [inst_2 : _root_.Module K V],   LinearIndependent K Subtype.val
参数：K : Type u_3；V : Type u_4。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.ofVectorSpace_apply_self`：ofVectorSpace_apply_self (x : ofV
ectorSpaceIndex K V) : ofVectorSpace K V x = x
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
-/
theorem ofVectorSpaceIndex.linearIndependent :
    LinearIndependent K ((↑) : ofVectorSpaceIndex K V → V) := by
  convert! (ofVectorSpace K V).linearIndependent
  ext x
  rw [ofVectorSpace_apply_self]
/-
**Module.Basis.range_ofVectorSpace** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：range_ofVectorSpace : range (ofVectorSpace K V) = ofVectorSpaceIndex K V
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.range_extend`：range_extend (hs : LinearIndepOn K id s) : ra
nge (Basis.extend hs) = hs.extend (subset_univ _)
-/
theorem range_ofVectorSpace : range (ofVectorSpace K V) = ofVectorSpaceIndex K V :=
  range_extend _
/-
**Module.Basis.exists_basis** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：exists_basis : exists s : Set V, Nonempty (Basis s K V)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_basis : ∃ s : Set V, Nonempty (Basis s K V) :=
  ⟨ofVectorSpaceIndex K V, ⟨ofVectorSpace K V⟩⟩

end

end ExistsBasis

end Module.Basis

open Fintype

variable (K V)

/-
**VectorSpace.card_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：VectorSpace.card_fintype [Fintype K] [Fintype V] : exists n : Nat, card V 
= card K ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.card_fintype`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_
3 : Finty…
-/
theorem VectorSpace.card_fintype [Fintype K] [Fintype V] : ∃ n : ℕ, card V = card K ^ n := by
  classical
  exact ⟨card (Basis.ofVectorSpaceIndex K V), Module.card_fintype (Basis.ofVectorSpace K V)⟩

section AtomsOfSubmoduleLattice

variable {K V}

/-- For a module over a division ring, the span of a nonzero element is an atom of the
lattice of submodules. -/
/-
**nonzero_span_atom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nonzero_span_atom (v : V) (hv : v != 0) : IsAtom (span K {v} : Submodule K
 V)
参数：v : V；hv : v != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p

--- 原说明 ---
For a module over a division ring, the span of a nonzero element is an atom of t
he
lattice of submodules.
-/
theorem nonzero_span_atom (v : V) (hv : v ≠ 0) : IsAtom (span K {v} : Submodule K V) := by
  constructor
  · rw [Submodule.ne_bot_iff]
    exact ⟨v, ⟨mem_span_singleton_self v, hv⟩⟩
  · intro T hT
    by_contra h
    apply hT.2
    change span K {v} ≤ T
    simp_rw [span_singleton_le_iff_mem, ← Ne.eq_def, Submodule.ne_bot_iff] at *
    rcases h with ⟨s, ⟨hs, hz⟩⟩
    rcases mem_span_singleton.1 (hT.1 hs) with ⟨a, rfl⟩
    rcases eq_or_ne a 0 with rfl | h
    · simp only [zero_smul, ne_eq, not_true] at hz
    · rwa [T.smul_mem_iff h] at hs

/-- The atoms of the lattice of submodules of a module over a division ring are the
submodules equal to the span of a nonzero element of the module. -/
/-
**atom_iff_nonzero_span** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：atom_iff_nonzero_span (W : Submodule K V) : IsAtom W ↔ exists v != 0, W = 
span K {v}
参数：W : Submodule K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Submodule.span_singleton_eq_bot`：span_singleton_eq_bot : R ∙ x = ⊥ ↔ x =
 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `nonzero_span_atom`：nonzero_span_atom (v : V) (hv : v != 0) : IsAtom (spa
n K {v} : Submodule K V)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The atoms of the lattice of submodules of a module over a division ring are the
submodules equal to the span of a nonzero element of the module.
-/
theorem atom_iff_nonzero_span (W : Submodule K V) :
    IsAtom W ↔ ∃ v ≠ 0, W = span K {v} := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨hbot, h⟩ := h
    rcases (Submodule.ne_bot_iff W).1 hbot with ⟨v, ⟨hW, hv⟩⟩
    refine ⟨v, ⟨hv, ?_⟩⟩
    by_contra heq
    specialize h (span K {v})
    rw [span_singleton_eq_bot, lt_iff_le_and_ne] at h
    exact hv (h ⟨(span_singleton_le_iff_mem v W).2 hW, Ne.symm heq⟩)
  · rcases h with ⟨v, ⟨hv, rfl⟩⟩
    exact nonzero_span_atom v hv

/-- The lattice of submodules of a module over a division ring is atomistic. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lattice of submodules of a module over a division ring is atomistic.
-/
instance : IsAtomistic (Submodule K V) :=
  CompleteLattice.isAtomistic_iff.2 fun W => by
    refine ⟨_, submodule_eq_sSup_le_nonzero_spans W, ?_⟩
    rintro _ ⟨w, ⟨_, ⟨hw, rfl⟩⟩⟩
    exact nonzero_span_atom w hw

end AtomsOfSubmoduleLattice

variable {K V}

/-
**LinearMap.exists_leftInverse_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.exists_leftInverse_of_injective (f : V ->ₗ[K] V') (hf_inj : Line
arMap.ker f = ⊥) : exists g : V' ->ₗ[K] V, g.comp f = LinearMap.id
参数：f : V ->ₗ[K] V'；hf_inj : LinearMap.ker f = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `LinearIndepOn.image`：LinearIndepOn.image {s : Set M} {f : M ->ₗ[R] M'} (
hs : LinearIndepOn R id s) (hf_inj : Disjoint (span R s) (LinearMap.ker f)) : Li
nearIndep…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coe_ofVectorSpace`：coe_ofVectorSpace : ⇑(ofVectorSpace K V)
 = ((↑) : _ -> _)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `Module.Basis.range_ofVectorSpace`：range_ofVectorSpace : range (ofVectorS
pace K V) = ofVectorSpaceIndex K V
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `LinearIndepOn.subset_extend`：LinearIndepOn.subset_extend (hs : LinearInd
epOn K v s) (hst : s subseteq t) : s subseteq hs.extend hst
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Module.Basis.extend_apply_self`：extend_apply_self (hs : LinearIndepOn K 
id s) (x : hs.extend _) : Basis.extend hs x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Basis.ofVectorSpace_apply_self`：ofVectorSpace_apply_self (x : ofV
ectorSpaceIndex K V) : ofVectorSpace K V x = x
· 使用定理 `Module.Basis.constr_basis`：constr_basis (f : ι -> M') (i : ι) : (constr 
(M'
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
-/
theorem LinearMap.exists_leftInverse_of_injective (f : V →ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) :
    ∃ g : V' →ₗ[K] V, g.comp f = LinearMap.id := by
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
  refine ⟨(hC.constr ℕ : _ → _) (C.domRestrict (invFun f)), hB.ext fun b => ?_⟩
  rw [image_subset_iff] at BC
  have fb_eq : f b = hC ⟨f b, BC b.2⟩ := by
    change f b = Basis.extend this _
    simp_rw [Basis.extend_apply_self]
  dsimp
  rw [Basis.ofVectorSpace_apply_self, fb_eq, hC.constr_basis]
  exact leftInverse_invFun (LinearMap.ker_eq_bot.1 hf_inj) _

/-- The left inverse of `f : E →ₗ[𝕜] F`.

If `f` is not injective, then we use the junk value `0`. -/
noncomputable
/-
**LinearMap.leftInverse** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LinearMap.leftInverse (f : V ->ₗ[K] V') : V' ->ₗ[K] V
参数：f : V ->ₗ[K] V'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_leftInverse_of_injective`：LinearMap.exists_leftInverse_
of_injective (f : V ->ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) : exists g : V' ->
ₗ[K] V, g.comp f = LinearMap.id
-/
def LinearMap.leftInverse (f : V →ₗ[K] V') : V' →ₗ[K] V :=
  if h_inj : LinearMap.ker f = ⊥ then
  (f.exists_leftInverse_of_injective h_inj).choose
  else 0
/-
**LinearMap.leftInverse_comp_of_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.leftInverse_comp_of_inj {f : V ->ₗ[K] V'} (h_inj : LinearMap.ker
 f = ⊥) : f.leftInverse ∘ₗ f = LinearMap.id
参数：h_inj : LinearMap.ker f = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_leftInverse_of_injective`：LinearMap.exists_leftInverse_
of_injective (f : V ->ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) : exists g : V' ->
ₗ[K] V, g.comp f = LinearMap.id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem LinearMap.leftInverse_comp_of_inj {f : V →ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) :
    f.leftInverse ∘ₗ f = LinearMap.id := by
  simpa [leftInverse, h_inj] using (f.exists_leftInverse_of_injective h_inj).choose_spec

/-- If `f` is injective, then the left inverse composed with `f` is the identity. -/
/-
**LinearMap.leftInverse_apply_of_inj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.leftInverse_apply_of_inj {f : V ->ₗ[K] V'} (h_inj : LinearMap.ke
r f = ⊥) (x : V) : f.leftInverse (f x) = x
参数：h_inj : LinearMap.ker f = ⊥；x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.leftInverse_comp_of_inj`：LinearMap.leftInverse_comp_of_inj {f 
: V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) : f.leftInverse ∘ₗ f = LinearMap.id

--- 原说明 ---
If `f` is injective, then the left inverse composed with `f` is the identity.
-/
theorem LinearMap.leftInverse_apply_of_inj {f : V →ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) (x : V) :
    f.leftInverse (f x) = x :=
  LinearMap.ext_iff.mp (f.leftInverse_comp_of_inj h_inj) x
/-
**Submodule.exists_isCompl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.exists_isCompl (p : Submodule K V) : exists q : Submodule K V, I
sCompl p q
参数：p : Submodule K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isCompl_of_proj`：isCompl_of_proj {f : E ->ₗ[R] p} (hf : forall
 x : p, f x = x) : IsCompl p (ker f)
· 使用定理 `LinearMap.leftInverse_apply_of_inj`：LinearMap.leftInverse_apply_of_inj {
f : V ->ₗ[K] V'} (h_inj : LinearMap.ker f = ⊥) (x : V) : f.leftInverse (f x) = x
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
-/
theorem Submodule.exists_isCompl (p : Submodule K V) : ∃ q : Submodule K V, IsCompl p q :=
  ⟨LinearMap.ker p.subtype.leftInverse,
    LinearMap.isCompl_of_proj <| LinearMap.leftInverse_apply_of_inj p.ker_subtype⟩
/-
**Submodule.complementedLattice** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Submodule.complementedLattice : ComplementedLattice (Submodule K V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_isCompl`：Submodule.exists_isCompl (p : Submodule K V) :
 exists q : Submodule K V, IsCompl p q
-/
instance Submodule.complementedLattice : ComplementedLattice (Submodule K V) :=
  ⟨Submodule.exists_isCompl⟩

/-- Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the whole
space. -/
/-
**LinearMap.exists_extend** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.exists_extend {p : Submodule K V} (f : p ->ₗ[K] V') : exists g :
 V ->ₗ[K] V', g.comp p.subtype = f
参数：f : p ->ₗ[K] V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_leftInverse_of_injective`：LinearMap.exists_leftInverse_
of_injective (f : V ->ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) : exists g : V' ->
ₗ[K] V, g.comp f = LinearMap.id
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `LinearMap.comp_id`：comp_id : f.comp id = f

--- 原说明 ---
Any linear map `f : p →ₗ[K] V'` defined on a subspace `p` can be extended to the
 whole
space.
-/
theorem LinearMap.exists_extend {p : Submodule K V} (f : p →ₗ[K] V') :
    ∃ g : V →ₗ[K] V', g.comp p.subtype = f :=
  let ⟨g, hg⟩ := p.subtype.exists_leftInverse_of_injective p.ker_subtype
  ⟨f.comp g, by rw [LinearMap.comp_assoc, hg, f.comp_id]⟩
/-
**LinearMap.exists_extend_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.exists_extend_of_notMem {p : Submodule K V} {v : V} (f : p ->ₗ[K
] V') (hv : v ∉ p) (y : V') : exists g : V ->ₗ[K] V', g.comp p.subtype = f ∧ g v
 = y
参数：f : p ->ₗ[K] V'；hv : v ∉ p；y : V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_extend`：LinearMap.exists_extend {p : Submodule K V} (f 
: p ->ₗ[K] V') : exists g : V ->ₗ[K] V', g.comp p.subtype = f
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Submodule.mem_sup_left`：mem_sup_left {S T : Submodule R M} : forall {x :
 M}, x in S -> x in S ⊔ T
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LinearPMap.supSpanSingleton_apply_mk_of_mem`：supSpanSingleton_apply_mk_o
f_mem (f : E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain) {x' : E} (hx' : (x'
 : E) in f.domain) : f.supSpanSin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.mem_sup_right`：mem_sup_right {S T : Submodule R M} : forall {x
 : M}, x in T -> x in S ⊔ T
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `LinearPMap.supSpanSingleton_apply_self`：supSpanSingleton_apply_self (f :
 E ->ₛₗ.[σ] F) {x : E} (y : F) (hx : x ∉ f.domain) : f.supSpanSingleton x y hx ⟨
x, mem_sup_right mem_span_si…
-/
theorem LinearMap.exists_extend_of_notMem {p : Submodule K V} {v : V} (f : p →ₗ[K] V')
    (hv : v ∉ p) (y : V') : ∃ g : V →ₗ[K] V', g.comp p.subtype = f ∧ g v = y := by
  rcases (LinearPMap.supSpanSingleton ⟨p, f⟩ v y hv).toFun.exists_extend with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · ext x
    have := LinearPMap.supSpanSingleton_apply_mk_of_mem ⟨p, f⟩ y hv x.2
    simpa using! congr($hg _).trans this
  · have := LinearPMap.supSpanSingleton_apply_self ⟨p, f⟩ y hv
    simpa using! congr($hg _).trans this

open Submodule LinearMap
/-
**Submodule.exists_le_ker_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.exists_le_ker_of_notMem {p : Submodule K V} {v : V} (hv : v ∉ p)
 : exists f : V ->ₗ[K] K, f v != 0 ∧ p <= ker f
参数：hv : v ∉ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_extend_of_notMem`：LinearMap.exists_extend_of_notMem {p 
: Submodule K V} {v : V} (f : p ->ₗ[K] V') (hv : v ∉ p) (y : V') : exists g : V 
->ₗ[K] V', g.comp p.sub…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Submodule.exists_le_ker_of_notMem {p : Submodule K V} {v : V} (hv : v ∉ p) :
    ∃ f : V →ₗ[K] K, f v ≠ 0 ∧ p ≤ ker f := by
  rcases LinearMap.exists_extend_of_notMem (0 : p →ₗ[K] K) hv 1 with ⟨f, hpf, hfv⟩
  refine ⟨f, by simp [hfv], fun x hx ↦ ?_⟩
  simpa using congr($hpf ⟨x, hx⟩)

/-- If `V` and `V'` are nontrivial vector spaces over a field `K`, the space of `K`-linear maps
between them is nontrivial. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `V` and `V'` are nontrivial vector spaces over a field `K`, the space of `K`-
linear maps
between them is nontrivial.
-/
instance [Nontrivial V] [Nontrivial V'] : Nontrivial (V →ₗ[K] V') := by
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨w, hw⟩ := exists_ne (0 : V')
  have : v ∉ (⊥ : Submodule K V) := by simp only [mem_bot, hv, not_false_eq_true]
  obtain ⟨g, _, hg⟩ := LinearMap.exists_extend_of_notMem (K := K) 0 this w
  exact ⟨g, 0, DFunLike.ne_iff.mpr ⟨v, by simp_all⟩⟩

/-- If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero linear map
`f : V →ₗ[K] K` such that `p ≤ ker f`. -/
/-
**Submodule.exists_le_ker_of_lt_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.exists_le_ker_of_lt_top (p : Submodule K V) (hp : p < ⊤) : exist
s (f : V ->ₗ[K] K), f != 0 ∧ p <= ker f
参数：p : Submodule K V；hp : p < ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.exists_of_lt`：exists_of_lt : p < q -> exists x in q, x ∉ p
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.exists_le_ker_of_notMem`：Submodule.exists_le_ker_of_notMem {p 
: Submodule K V} {v : V} (hv : v ∉ p) : exists f : V ->ₗ[K] K, f v != 0 ∧ p <= k
er f
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y

--- 原说明 ---
If `p < ⊤` is a subspace of a vector space `V`, then there exists a nonzero line
ar map
`f : V →ₗ[K] K` such that `p ≤ ker f`.
-/
theorem Submodule.exists_le_ker_of_lt_top (p : Submodule K V) (hp : p < ⊤) :
    ∃ (f : V →ₗ[K] K), f ≠ 0 ∧ p ≤ ker f := by
  rcases SetLike.exists_of_lt hp with ⟨v, -, hpv⟩
  rcases exists_le_ker_of_notMem hpv with ⟨f, hfv, hpf⟩
  exact ⟨f, ne_of_apply_ne (· v) hfv, hpf⟩
/-
**quotient_prod_linearEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：quotient_prod_linearEquiv (p : Submodule K V) : Nonempty (((V ⧸ p) × p) ≃ₗ
[K] V)
参数：p : Submodule K V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_isCompl`：Submodule.exists_isCompl (p : Submodule K V) :
 exists q : Submodule K V, IsCompl p q
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
-/
theorem quotient_prod_linearEquiv (p : Submodule K V) : Nonempty (((V ⧸ p) × p) ≃ₗ[K] V) :=
  let ⟨q, hq⟩ := p.exists_isCompl
  Nonempty.intro <|
    ((quotientEquivOfIsCompl p q hq).prodCongr (LinearEquiv.refl _ _)).trans
      (prodEquivOfIsCompl q p hq.symm)

end DivisionRing

section Field

open Submodule LinearMap Module

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable {f : V →ₗ[K] K} {v : V}

set_option backward.isDefEq.respectTransparency false in
/-- In a vector space, given a nonzero linear form `f`,
a nonzero vector `v` such that `f v ≠ 0`,
there exists a basis `b` with an index `i`
such that `v = b i` and `f = (f v) • b.coord i`. -/
/-
**exists_basis_of_pairing_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_basis_of_pairing_ne_zero (hfv : f v != 0) : exists (n : Set V) (b :
 Module.Basis n K V) (i : n), v = b i ∧ f = (f v) • b.coord i
参数：hfv : f v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndepOn.id_insert`：∀ {K : Type u_3} {V : Type u} [inst : DivisionR
ing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {s : Set V}   {x :
 V}, LinearIn…
· 使用定理 `LinearIndepOn.image`：LinearIndepOn.image {s : Set M} {f : M ->ₗ[R] M'} (
hs : LinearIndepOn R id s) (hf_inj : Disjoint (span R s) (LinearMap.ker f)) : Li
nearIndep…
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
In a vector space, given a nonzero linear form `f`,
a nonzero vector `v` such that `f v ≠ 0`,
there exists a basis `b` with an index `i`
such that `v = b i` and `f = (f v) • b.coord i`.
-/
theorem exists_basis_of_pairing_ne_zero
    (hfv : f v ≠ 0) :
    ∃ (n : Set V) (b : Module.Basis n K V) (i : n),
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
  have H₂ : ⊤ ≤ span K n := by
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
    rw [← mem_ker, ← hs, Basis.coe_mk]
    apply subset_span
    apply Or.resolve_left (Set.mem_insert_iff.mpr j.prop)
    simp [← hi, b, Subtype.coe_inj, Ne.symm h]

/-- In a vector space, given a nonzero linear form `f`,
a nonzero vector `v` such that `f v = 0`,
there exists a basis `b` with two distinct indices `i`, `j`
such that `v = b i` and `f = b.coord j`. -/
/-
**exists_basis_of_pairing_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_basis_of_pairing_eq_zero (hfv : f v = 0) (hf : f != 0) (hv : v != 0
) : exists (n : Set V) (b : Basis n K V) (i j : n), i != j ∧ v = b i ∧ f = b.coo
rd j
参数：hfv : f v = 0；hf : f != 0；hv : v != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Module.Basis.coe_extend`：coe_extend (hs : LinearIndepOn K id s) : ⇑(Basi
s.extend hs) = ((↑) : _ -> _)
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `LinearIndepOn.subset_extend`：LinearIndepOn.subset_extend (hs : LinearInd
epOn K v s) (hst : s subseteq t) : s subseteq hs.extend hst
· 使用定理 `LinearIndepOn.id_insert`：∀ {K : Type u_3} {V : Type u} [inst : DivisionR
ing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {s : Set V}   {x :
 V}, LinearIn…
· 使用定理 `LinearIndepOn.image`：LinearIndepOn.image {s : Set M} {f : M ->ₗ[R] M'} (
hs : LinearIndepOn R id s) (hf_inj : Disjoint (span R s) (LinearMap.ker f)) : Li
nearIndep…
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
In a vector space, given a nonzero linear form `f`,
a nonzero vector `v` such that `f v = 0`,
there exists a basis `b` with two distinct indices `i`, `j`
such that `v = b i` and `f = b.coord j`.
-/
theorem exists_basis_of_pairing_eq_zero
    (hfv : f v = 0) (hf : f ≠ 0) (hv : v ≠ 0) :
    ∃ (n : Set V) (b : Basis n K V) (i j : n),
      i ≠ j ∧ v = b i ∧ f = b.coord j := by
  lift v to ker f using hfv
  have : LinearIndepOn K _root_.id {v} := by simpa using hv
  set b₁ : Basis _ K (ker f) := .extend this
  obtain ⟨w, hw⟩ : ∃ w, f w = 1 := by
    simp only [ne_eq, DFunLike.ext_iff, not_forall] at hf
    rcases hf with ⟨w, hw⟩
    use (f w)⁻¹ • w
    simp_all
  set s : Set V := (ker f).subtype '' Set.range b₁
  have hs : span K s = ker f := by
    simp only [s, span_image]
    simp
  have hvs : ↑v ∈ s := by
    refine ⟨v, ?_, by simp⟩
    simp [b₁, this.subset_extend _ _]
  set n := insert w s
  have H₁ : LinearIndepOn K _root_.id n := by
    apply LinearIndepOn.id_insert
    · apply LinearIndepOn.image
      · exact b₁.linearIndependent.linearIndepOn_id
      · simp
    · simp [hs, hw]
  have H₂ : ⊤ ≤ span K n := by
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
    rw [Basis.coord_apply, Basis.repr_self]
    simp only [b]
    rcases i with ⟨x, rfl | ⟨x, hx, rfl⟩⟩
    · simp [hw]
    · suffices x ≠ w by simp [this]
      apply_fun f
      simp [hw]

end Field

