/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Sigma
public import Mathlib.Data.Fintype.OfMap

/-!
# fintype instances for sigma types
-/

public section


open Function

open Nat

universe u v

variable {ι α : Type*} {κ : ι -> Type*} [Π i, Fintype (κ i)]

open Finset

/--
lemma `Set.biUnion_finsetSigma_univ` / 引理 `Set.biUnion_finsetSigma_univ`

English:
lemma Set.biUnion_finsetSigma_univ
  given: (s : Finset ι) (f : Sigma κ -> Set α)
  proof: by aesop

中文:
引理 集合.biUnion_finsetSigma_univ
  条件: (s : 有限集 ι) (f : 依赖和类型 κ -> 集合 α)
  证明: by aesop
-/
lemma Set.biUnion_finsetSigma_univ (s : Finset ι) (f : Sigma κ -> Set α) :
    ⋃ ij in s.sigma fun _ => Finset.univ, f ij = ⋃ i in s, ⋃ j, f ⟨i, j⟩ := by aesop

/--
lemma `Set.biUnion_finsetSigma_univ'` / 引理 `Set.biUnion_finsetSigma_univ'`

English:
lemma Set.biUnion_finsetSigma_univ'
  given: (s : Finset ι) (f : Π i, κ i -> Set α)
  proof: by aesop

中文:
引理 集合.biUnion_finsetSigma_univ'
  条件: (s : 有限集 ι) (f : Π i, κ i -> 集合 α)
  证明: by aesop
-/
lemma Set.biUnion_finsetSigma_univ' (s : Finset ι) (f : Π i, κ i -> Set α) :
    ⋃ i in s, ⋃ j, f i j = ⋃ ij in s.sigma fun _ => Finset.univ, f ij.1 ij.2 := by aesop

/--
lemma `Set.biInter_finsetSigma_univ` / 引理 `Set.biInter_finsetSigma_univ`

English:
lemma Set.biInter_finsetSigma_univ
  given: (s : Finset ι) (f : Sigma κ -> Set α)
  proof: by aesop

中文:
引理 集合.bi整数er_finsetSigma_univ
  条件: (s : 有限集 ι) (f : 依赖和类型 κ -> 集合 α)
  证明: by aesop
-/
lemma Set.biInter_finsetSigma_univ (s : Finset ι) (f : Sigma κ -> Set α) :
    ⋂ ij in s.sigma fun _ => Finset.univ, f ij = ⋂ i in s, ⋂ j, f ⟨i, j⟩ := by aesop

attribute [local simp] Sigma.forall in
/--
lemma `Set.biInter_finsetSigma_univ'` / 引理 `Set.biInter_finsetSigma_univ'`

English:
lemma Set.biInter_finsetSigma_univ'
  given: (s : Finset ι) (f : Π i, κ i -> Set α)
  proof: by aesop

中文:
引理 集合.bi整数er_finsetSigma_univ'
  条件: (s : 有限集 ι) (f : Π i, κ i -> 集合 α)
  证明: by aesop
-/
lemma Set.biInter_finsetSigma_univ' (s : Finset ι) (f : Π i, κ i -> Set α) :
    ⋂ i in s, ⋂ j, f i j = ⋂ ij in s.sigma fun _ => Finset.univ, f ij.1 ij.2 := by aesop

variable [Fintype ι]

/--
Instance `Sigma.instFintype` / 实例 `Sigma.instFintype`

English:
instance Sigma.instFintype
  signature: : Fintype (Σ i, κ i)
  body: ⟨univ.sigma fun _ => univ, by simp⟩

中文:
实例 依赖和类型.instFintype
  签名: : 有限类型 (Σ i, κ i)
  定义体: ⟨univ.sigma fun _ => univ, by simp⟩

Depends on / 依赖: univ.sigma
-/
instance Sigma.instFintype : Fintype (Σ i, κ i) := ⟨univ.sigma fun _ => univ, by simp⟩
/--
Instance `PSigma.instFintype` / 实例 `PSigma.instFintype`

English:
instance PSigma.instFintype
  signature: : Fintype (Σ' i, κ i)
  body: .ofEquiv _ (Equiv.psigmaEquivSigma _).symm

中文:
实例 命题和类型.instFintype
  签名: : 有限类型 (Σ' i, κ i)
  定义体: .ofEquiv _ (Equiv.psigmaEquivSigma _).symm

Depends on / 依赖: Equiv.psigmaEquivSigma, ofEquiv, psigmaEquivSigma
-/
instance PSigma.instFintype : Fintype (Σ' i, κ i) := .ofEquiv _ (Equiv.psigmaEquivSigma _).symm

/--
lemma `Finset.univ_sigma_univ` / 引理 `Finset.univ_sigma_univ`

English:
lemma Finset.univ_sigma_univ
  statement: univ.sigma (fun _ => univ) = (univ : Finset (Σ i, κ i))
  proof: rfl

中文:
引理 有限集.univ_sigma_univ
  结论: univ.sigma (fun _ => univ) = (univ : 有限集 (Σ i, κ i))
  证明: rfl
-/
@[simp] lemma Finset.univ_sigma_univ : univ.sigma (fun _ => univ) = (univ : Finset (Σ i, κ i)) := rfl
