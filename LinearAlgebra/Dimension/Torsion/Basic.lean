/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Subsingleton

/-!
# Rank and torsion

## Main statements

- `rank_quotient_eq_of_le_torsion` : `rank M/N = rank M` if `N ≤ torsion M`.
- `finrank_quotient_eq_of_le_torsion` : `finrank M/N = finrank M` if `N ≤ torsion M`.
- `finrank_quotient_torsion_eq` : `finrank ℤ (M / torsion M) = finrank ℤ M` for an additive
  commutative group `M`.
-/

public section

open Submodule

set_option backward.isDefEq.respectTransparency false in
/-
**rank_quotient_eq_of_le_torsion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_quotient_eq_of_le_torsion {R M : Type*} [CommRing R] [AddCommGroup M]
 [Module R M] {M' : Submodule R M} (hN : M' <= torsion R M) : Module.rank R (M ⧸
 M') = Module.rank R M
参数：hN : M' <= torsion R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `rank_quotient_le`：rank_quotient_le (p : Submodule R M) : Module.rank R (
M ⧸ p) <= Module.rank R M
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `LinearIndepOn.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v : ι
 → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] (s :…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem rank_quotient_eq_of_le_torsion {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {M' : Submodule R M} (hN : M' ≤ torsion R M) : Module.rank R (M ⧸ M') = Module.rank R M :=
  (rank_quotient_le M').antisymm <| by
    nontriviality R
    rw [Module.rank]
    refine ciSup_le fun ⟨s, hs⟩ ↦ LinearIndependent.cardinal_le_rank (v := (M'.mkQ ·)) ?_
    rw [LinearIndepOn, linearIndependent_iff'] at hs
    simp_rw [linearIndependent_iff', ← map_smul, ← map_sum, mkQ_apply, Quotient.mk_eq_zero]
    intro t g hg i hi
    obtain ⟨r, hg⟩ := hN hg
    simp_rw [Finset.smul_sum, Submonoid.smul_def, smul_smul] at hg
    exact r.prop.2 _ (mul_comm (g i) r ▸ hs t _ hg i hi)
/-
**finrank_quotient_eq_of_le_torsion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_quotient_eq_of_le_torsion {R M : Type*} [CommRing R] [AddCommGroup
 M] [Module R M] {M' : Submodule R M} (hN : M' <= torsion R M) : Module.finrank 
R (M ⧸ M') = Module.finrank R M
参数：hN : M' <= torsion R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `rank_quotient_eq_of_le_torsion`：rank_quotient_eq_of_le_torsion {R M : Ty
pe*} [CommRing R] [AddCommGroup M] [Module R M] {M' : Submodule R M} (hN : M' <=
 torsion R M) : Modu…
-/
theorem finrank_quotient_eq_of_le_torsion {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {M' : Submodule R M} (hN : M' ≤ torsion R M) :
    Module.finrank R (M ⧸ M') = Module.finrank R M :=
  congr_arg Cardinal.toNat (rank_quotient_eq_of_le_torsion hN)

/-- Quotienting an additive commutative group by its torsion subgroup does not change its
`ℤ`-`finrank`. -/
/-
**finrank_quotient_torsion_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_quotient_torsion_eq {M : Type*} [AddCommGroup M] : Module.finrank 
Int (M ⧸ (AddCommGroup.torsion M).toIntSubmodule) = Module.finrank Int M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finrank_quotient_eq_of_le_torsion`：finrank_quotient_eq_of_le_torsion {R 
M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {M' : Submodule R M} (hN :
 M' <= torsion R M) : M…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.torsion_int`：torsion_int {G} [AddCommGroup G] : (torsion Int G
).toAddSubgroup = AddCommGroup.torsion G
· 使用定理 `Submodule.toAddSubgroup_toIntSubmodule`：Submodule.toAddSubgroup_toIntSub
module (S : Submodule Int M) : S.toAddSubgroup.toIntSubmodule = S

--- 原说明 ---
Quotienting an additive commutative group by its torsion subgroup does not chang
e its
`ℤ`-`finrank`.
-/
theorem finrank_quotient_torsion_eq {M : Type*} [AddCommGroup M] :
    Module.finrank ℤ (M ⧸ (AddCommGroup.torsion M).toIntSubmodule) = Module.finrank ℤ M :=
  finrank_quotient_eq_of_le_torsion <| le_of_eq <| by
    rw [← Submodule.torsion_int, Submodule.toAddSubgroup_toIntSubmodule]
