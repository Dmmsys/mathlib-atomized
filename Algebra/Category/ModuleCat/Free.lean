/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exact sequences with free modules

This file proves results about linear independence and span in exact sequences of modules.

## Main theorems

* `linearIndependent_shortExact`: Given a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of
  `R`-modules and linearly independent families `v : ι → X₁` and `w : ι' → X₃`, we get a linearly
  independent family `ι ⊕ ι' → X₂`
* `span_rightExact`: Given an exact sequence `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules and spanning
  families `v : ι → X₁` and `w : ι' → X₃`, we get a spanning family `ι ⊕ ι' → X₂`
* Using `linearIndependent_shortExact` and `span_rightExact`, we prove `free_shortExact`: In a
  short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` where `X₁` and `X₃` are free, `X₂` is free as well.

## Tags
linear algebra, module, free

-/

@[expose] public section

open CategoryTheory Module

namespace ModuleCat

variable {ι ι' R : Type*} [Ring R] {S : ShortComplex (ModuleCat R)}
  (hS : S.Exact) (hS' : S.ShortExact) {v : ι → S.X₁}

open CategoryTheory Submodule Set

section LinearIndependent

variable (hv : LinearIndependent R v) {u : ι ⊕ ι' → S.X₂}
  (hw : LinearIndependent R (S.g ∘ u ∘ Sum.inr))
  (hm : Mono S.f) (huv : u ∘ Sum.inl = S.f ∘ v)

section
include hS hw huv

/-
**ModuleCat.disjoint_span_sum** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：disjoint_span_sum : Disjoint (span R (range (u ∘ Sum.inl))) (span R (range
 (u ∘ Sum.inr)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.range_comp_subset_range`：range_comp_subset_range (f : α -> β) (g : β
 -> γ) : range (g ∘ f) subseteq range g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_range`：coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] 
M₂) : (range f : Set M₂) = Set.range f
· 使用定理 `Submodule.span_eq`：span_eq : span R (p : Set M) = p
· 使用定理 `CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker`：∀ {R : Type u}
 [inst : Ring R] {S : CategoryTheory.ShortComplex (ModuleCat R)},   S.Exact → (M
oduleCat.Hom.hom S.f).range = (ModuleCat.Hom.h…
· 使用定理 `Submodule.range_ker_disjoint`：Submodule.range_ker_disjoint {f : M ->ₗ[R]
 M'} (hv : LinearIndependent R (f ∘ v)) : Disjoint (span R (range v)) (LinearMap
.ker f)
-/
theorem disjoint_span_sum : Disjoint (span R (range (u ∘ Sum.inl)))
    (span R (range (u ∘ Sum.inr))) := by
  rw [huv, disjoint_comm]
  refine Disjoint.mono_right (span_mono (range_comp_subset_range _ _)) ?_
  rw [← LinearMap.coe_range, span_eq (LinearMap.range S.f.hom), hS.moduleCat_range_eq_ker]
  exact range_ker_disjoint hw

include hv hm in
/-- In the commutative diagram
```
             f     g
    0 --→ X₁ --→ X₂ --→ X₃
          ↑      ↑      ↑
         v|     u|     w|
          ι  → ι ⊕ ι' ← ι'
```
where the top row is an exact sequence of modules and the maps on the bottom are `Sum.inl` and
`Sum.inr`. If `u` is injective and `v` and `w` are linearly independent, then `u` is linearly
independent. -/
/-
**ModuleCat.linearIndependent_leftExact** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：linearIndependent_leftExact : LinearIndependent R u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_sum`：linearIndependent_sum {v : ι oplus ι' -> M} : Lin
earIndependent R v ↔ LinearIndependent R (v ∘ Sum.inl) ∧ LinearIndependent R (v 
∘ Sum.inr) …
· 使用定理 `LinearMap.linearIndependent_iff`：∀ {ι : Type u'} {R : Type u_2} {M : Typ
e u_4} {M' : Type u_5} {v : ι → M} [inst : Ring R] [inst_1 : AddCommGroup M]   [
inst_2 : AddCommGroup…
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ModuleCat.mono_iff_injective`：mono_iff_injective : Mono f ↔ Function.Inj
ective f
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `ModuleCat.disjoint_span_sum`：disjoint_span_sum : Disjoint (span R (range
 (u ∘ Sum.inl))) (span R (range (u ∘ Sum.inr)))

--- 原说明 ---
In the commutative diagram
```
             f     g
    0 --→ X₁ --→ X₂ --→ X₃
          ↑      ↑      ↑
         v|     u|     w|
          ι  → ι ⊕ ι' ← ι'
```
where the top row is an exact sequence of modules and the maps on the bottom are
 `Sum.inl` and
`Sum.inr`. If `u` is injective and `v` and `w` are linearly independent, then `u
` is linearly
independent.
-/
theorem linearIndependent_leftExact : LinearIndependent R u := by
  rw [linearIndependent_sum]
  refine ⟨?_, LinearIndependent.of_comp S.g.hom hw, disjoint_span_sum hS hw huv⟩
  rw [huv, LinearMap.linearIndependent_iff S.f.hom]; swap
  · rw [LinearMap.ker_eq_bot, ← mono_iff_injective]
    infer_instance
  exact hv

end

include hS' hv in
/-- Given a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules and linearly independent
families `v : ι → N` and `w : ι' → P`, we get a linearly independent family `ι ⊕ ι' → M` -/
/-
**ModuleCat.linearIndependent_shortExact** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：linearIndependent_shortExact {w : ι' -> S.X₃} (hw : LinearIndependent R w)
 : LinearIndependent R (Sum.elim (S.f ∘ v) (S.g.hom.toFun.invFun ∘ w))
参数：hw : LinearIndependent R w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.linearIndependent_leftExact`：linearIndependent_leftExact : Lin
earIndependent R u
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.exact`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.rightInverse_invFun`：rightInverse_invFun (hf : Surjective f) : 
RightInverse (invFun f) f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.epi_g`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms C]   {S : CategoryTheory.Sho…
· 使用定理 `CategoryTheory.ShortComplex.ShortExact.mono_f`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroMor
phisms C]   {S : CategoryTheory.Sho…

--- 原说明 ---
Given a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules and linearly 
independent
families `v : ι → N` and `w : ι' → P`, we get a linearly independent family `ι ⊕
 ι' → M`
-/
theorem linearIndependent_shortExact {w : ι' → S.X₃} (hw : LinearIndependent R w) :
    LinearIndependent R (Sum.elim (S.f ∘ v) (S.g.hom.toFun.invFun ∘ w)) := by
  apply linearIndependent_leftExact hS'.exact hv _ hS'.mono_f rfl
  dsimp
  convert! hw
  ext
  apply Function.rightInverse_invFun ((epi_iff_surjective _).mp hS'.epi_g)

end LinearIndependent

section Span

include hS in
/-- In the commutative diagram
```
    f     g
 X₁ --→ X₂ --→ X₃
 ↑      ↑      ↑
v|     u|     w|
 ι  → ι ⊕ ι' ← ι'
```
where the top row is an exact sequence of modules and the maps on the bottom are `Sum.inl` and
`Sum.inr`. If `v` spans `X₁` and `w` spans `X₃`, then `u` spans `X₂`. -/
/-
**ModuleCat.span_exact** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：span_exact {β : Type*} {u : ι oplus β -> S.X₂} (huv : u ∘ Sum.inl = S.f ∘ 
v) (hv : ⊤ <= span R (range v)) (hw : ⊤ <= span R (range (S.g ∘ u ∘ Sum.inr))) :
 ⊤ <= span R (range u)
参数：huv : u ∘ Sum.inl = S.f ∘ v；hv : ⊤ <= span R (range v)；hw : ⊤ <= span R (rang
e (S.g ∘ u ∘ Sum.inr))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mem_span_range_iff_exists_finsupp`：mem_span_range_iff_exists_fin
supp {v : α -> M} {x : M} : x in span R (range v) ↔ exists c : α ->₀ R, (c.sum f
un i a => a • v i) = x
· 使用定理 `CategoryTheory.ShortComplex.Exact.moduleCat_range_eq_ker`：∀ {R : Type u}
 [inst : Ring R] {S : CategoryTheory.ShortComplex (ModuleCat R)},   S.Exact → (M
oduleCat.Hom.hom S.f).range = (ModuleCat.Hom.h…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Finsupp.sum_mapDomain_index_inj`：∀ {α : Type u_1} {β : Type u_2} {M : Ty
pe u_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f 
: α → β} {s : α →₀ M}…
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)

--- 原说明 ---
In the commutative diagram
```
    f     g
 X₁ --→ X₂ --→ X₃
 ↑      ↑      ↑
v|     u|     w|
 ι  → ι ⊕ ι' ← ι'
```
where the top row is an exact sequence of modules and the maps on the bottom are
 `Sum.inl` and
`Sum.inr`. If `v` spans `X₁` and `w` spans `X₃`, then `u` spans `X₂`.
-/
theorem span_exact {β : Type*} {u : ι ⊕ β → S.X₂} (huv : u ∘ Sum.inl = S.f ∘ v)
    (hv : ⊤ ≤ span R (range v))
    (hw : ⊤ ≤ span R (range (S.g ∘ u ∘ Sum.inr))) :
    ⊤ ≤ span R (range u) := by
  intro m _
  have hgm : S.g m ∈ span R (range (S.g ∘ u ∘ Sum.inr)) := hw mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hgm
  obtain ⟨cm, hm⟩ := hgm
  let m' : S.X₂ := Finsupp.sum cm fun j a ↦ a • (u (Sum.inr j))
  have hsub : m - m' ∈ LinearMap.range S.f.hom := by
    rw [hS.moduleCat_range_eq_ker]
    simp only [LinearMap.mem_ker, map_sub, sub_eq_zero]
    rw [← hm, map_finsuppSum]
    simp only [Function.comp_apply, map_smul]
  obtain ⟨n, hnm⟩ := hsub
  have hn : n ∈ span R (range v) := hv mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn
  obtain ⟨cn, hn⟩ := hn
  rw [← hn, map_finsuppSum] at hnm
  rw [← sub_add_cancel m m', ← hnm]
  simp only [map_smul]
  have hn' : (Finsupp.sum cn fun a b ↦ b • S.f (v a)) =
      (Finsupp.sum cn fun a b ↦ b • u (Sum.inl a)) := by
    congr; ext a b; rw [← Function.comp_apply (f := S.f), ← huv, Function.comp_apply]
  rw [hn']
  apply add_mem
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cn.mapDomain (Sum.inl)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inl_injective]
  · rw [Finsupp.mem_span_range_iff_exists_finsupp]
    use cm.mapDomain (Sum.inr)
    rw [Finsupp.sum_mapDomain_index_inj Sum.inr_injective]

include hS in
/-- Given an exact sequence `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules and spanning
families `v : ι → X₁` and `w : ι' → X₃`, we get a spanning family `ι ⊕ ι' → X₂` -/
/-
**ModuleCat.span_rightExact** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：span_rightExact {w : ι' -> S.X₃} (hv : ⊤ <= span R (range v)) (hw : ⊤ <= s
pan R (range w)) (hE : Epi S.g) : ⊤ <= span R (range (Sum.elim (S.f ∘ v) (S.g.ho
m.toFun.invFun ∘ w)))
参数：hv : ⊤ <= span R (range v)；hw : ⊤ <= span R (range w)；hE : Epi S.g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.span_exact`：span_exact {β : Type*} {u : ι oplus β -> S.X₂} (hu
v : u ∘ Sum.inl = S.f ∘ v) (hv : ⊤ <= span R (range v)) (hw : ⊤ <= span R (range
 (S.g ∘ u …
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Function.RightInverse.comp_eq_id`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse f g → g ∘ f = id
· 使用定理 `Function.rightInverse_invFun`：rightInverse_invFun (hf : Surjective f) : 
RightInverse (invFun f) f
· 使用定理 `ModuleCat.epi_iff_surjective`：epi_iff_surjective : Epi f ↔ Function.Surj
ective f
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f

--- 原说明 ---
Given an exact sequence `X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` of `R`-modules and spanning
families `v : ι → X₁` and `w : ι' → X₃`, we get a spanning family `ι ⊕ ι' → X₂`
-/
theorem span_rightExact {w : ι' → S.X₃} (hv : ⊤ ≤ span R (range v))
    (hw : ⊤ ≤ span R (range w)) (hE : Epi S.g) :
    ⊤ ≤ span R (range (Sum.elim (S.f ∘ v) (S.g.hom.toFun.invFun ∘ w))) := by
  refine span_exact hS ?_ hv ?_
  · simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inl]
  · convert! hw
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, Sum.elim_comp_inr]
    rw [ModuleCat.epi_iff_surjective] at hE
    rw [← Function.comp_assoc, Function.RightInverse.comp_eq_id (Function.rightInverse_invFun hE),
      Function.id_comp]

end Span

/-- In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, given bases for `X₁` and `X₃`
indexed by `ι` and `ι'` respectively, we get a basis for `X₂` indexed by `ι ⊕ ι'`. -/
noncomputable
/-
**ModuleCat.Basis.ofShortExact** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Basis`。
形式化陈述：{ι : Type u_1} →   {ι' : Type u_2} →     {R : Type u_3} →       [inst : Ri
ng R] →         {S : CategoryTheory.ShortComplex (ModuleCat R)} →           S.Sh
ortExact → Module.Basis ι R ↑S.X₁ → Module.Basis ι' R ↑S.X₃ → Module.Basis (ι ⊕ 
ι') R ↑S.X₂
参数：ModuleCat R；ι ⊕ ι'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Basis.ofShortExact
    (bN : Basis ι R S.X₁) (bP : Basis ι' R S.X₃) : Basis (ι ⊕ ι') R S.X₂ :=
  Basis.mk (linearIndependent_shortExact hS' bN.linearIndependent bP.linearIndependent)
    (span_rightExact hS'.exact (le_of_eq (bN.span_eq.symm)) (le_of_eq (bP.span_eq.symm)) hS'.epi_g)

include hS'

/-- In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, if `X₁` and `X₃` are free,
then `X₂` is free. -/
/-
**ModuleCat.free_shortExact** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：free_shortExact [Module.Free R S.X₁] [Module.Free R S.X₃] : Module.Free R 
S.X₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…

--- 原说明 ---
In a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0`, if `X₁` and `X₃` are free,
then `X₂` is free.
-/
theorem free_shortExact [Module.Free R S.X₁] [Module.Free R S.X₃] :
    Module.Free R S.X₂ :=
  Module.Free.of_basis (Basis.ofShortExact hS' (Module.Free.chooseBasis R S.X₁)
    (Module.Free.chooseBasis R S.X₃))
/-
**ModuleCat.free_shortExact_rank_add** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：free_shortExact_rank_add [Module.Free R S.X₁] [Module.Free R S.X₃] [Strong
RankCondition R] : Module.rank R S.X₂ = Module.rank R S.X₁ + Module.rank R S.X₃
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.free_shortExact`：free_shortExact [Module.Free R S.X₁] [Module.
Free R S.X₃] : Module.Free R S.X₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Free.rank_eq_card_chooseBasisIndex`：rank_eq_card_chooseBasisIndex
 : Module.rank R M = #(ChooseBasisIndex R M)
· 使用定理 `Cardinal.add_def`：add_def (α β : Type u) : #α + #β = #(α oplus β)
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
-/
theorem free_shortExact_rank_add [Module.Free R S.X₁] [Module.Free R S.X₃]
    [StrongRankCondition R] :
    Module.rank R S.X₂ = Module.rank R S.X₁ + Module.rank R S.X₃ := by
  have := free_shortExact hS'
  rw [Module.Free.rank_eq_card_chooseBasisIndex, Module.Free.rank_eq_card_chooseBasisIndex R S.X₁,
    Module.Free.rank_eq_card_chooseBasisIndex R S.X₃, Cardinal.add_def, Cardinal.eq]
  exact ⟨Basis.indexEquiv (Module.Free.chooseBasis R S.X₂) (Basis.ofShortExact hS'
    (Module.Free.chooseBasis R S.X₁) (Module.Free.chooseBasis R S.X₃))⟩
/-
**ModuleCat.free_shortExact_finrank_add** 是 Mathlib 中的一个定理，位于命名空间 `ModuleCat`。
形式化陈述：free_shortExact_finrank_add {n p : Nat} [Module.Free R S.X₁] [Module.Free 
R S.X₃] [Module.Finite R S.X₁] [Module.Finite R S.X₃] (hN : Module.finrank R S.X
₁ = n) (hP : Module.finrank R S.X₃ = p) [StrongRankCondition R] : finrank R S.X₂
 = n + p
参数：hN : Module.finrank R S.X₁ = n；hP : Module.finrank R S.X₃ = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ModuleCat.free_shortExact_rank_add`：free_shortExact_rank_add [Module.Fre
e R S.X₁] [Module.Free R S.X₃] [StrongRankCondition R] : Module.rank R S.X₂ = Mo
dule.rank R S.X₁ + Modul…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem free_shortExact_finrank_add {n p : ℕ} [Module.Free R S.X₁] [Module.Free R S.X₃]
    [Module.Finite R S.X₁] [Module.Finite R S.X₃]
    (hN : Module.finrank R S.X₁ = n)
    (hP : Module.finrank R S.X₃ = p)
    [StrongRankCondition R] :
    finrank R S.X₂ = n + p := by
  apply finrank_eq_of_rank_eq
  rw [free_shortExact_rank_add hS', ← hN, ← hP]
  simp only [Nat.cast_add, finrank_eq_rank]

end ModuleCat

