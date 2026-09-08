/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury, Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs
public import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-!
# Root data and root systems

This file contains basic results for root systems and root data.

## Main definitions / results:

* `RootPairing.ext`: In characteristic zero if there is no torsion, the correspondence between
  roots and coroots is unique.
* `RootSystem.ext`: In characteristic zero if there is no torsion, a root system is determined
  entirely by its roots.
* `RootPairing.mk'`: In characteristic zero if there is no torsion, to check that two finite
  families of roots and coroots form a root pairing, it is sufficient to check that they are
  stable under reflections.
* `RootSystem.mk'`: In characteristic zero if there is no torsion, to check that a finite family of
  roots form a root system, we do not need to check that the coroots are stable under reflections
  since this follows from the corresponding property for the roots.

-/

@[expose] public section

open Set Function
open Module hiding reflection
open Submodule (span)
open AddSubgroup (zmultiples)

noncomputable section

variable {ι R M N : Type*}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

section reflectionPerm

variable (p : M →ₗ[R] N →ₗ[R] R) (root : ι ↪ M) (coroot : ι ↪ N) (i j : ι)
  (h : ∀ i, MapsTo (preReflection (root i) (p.flip (coroot i)))
    (range root) (range root))
include h

set_option backward.privateInPublic true in
/-
**RootPairing.exist_eq_reflection_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `RootPairi
ng`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem exist_eq_reflection_of_mapsTo :
    ∃ k, root k = (preReflection (root i) (p.flip (coroot i))) (root j) :=
  h i (mem_range_self j)

variable (hp : ∀ i, p (root i) (coroot i) = 2)
include hp

set_option backward.privateInPublic true in
/-
**RootPairing.choose_choose_eq_of_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem choose_choose_eq_of_mapsTo :
    (exist_eq_reflection_of_mapsTo p root coroot i
      (exist_eq_reflection_of_mapsTo p root coroot i j h).choose h).choose = j := by
  refine root.injective ?_
  rw [(exist_eq_reflection_of_mapsTo p root coroot i _ h).choose_spec,
    (exist_eq_reflection_of_mapsTo p root coroot i j h).choose_spec]
  apply involutive_preReflection (x := root i) (hp i)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The bijection on the indexing set induced by reflection. -/
@[simps]
/-
**RootPairing.equiv_of_mapsTo** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] →  
               [inst_4 : _root_.Module R N] →                   (p : M →ₗ[R] N →
ₗ[R] R) →                     (root : ι ↪ M) →                       (coroot : ι
 ↪ N) →                         ι →                           (∀ (i : ι),       
                        Set.MapsTo (⇑(Module.preReflection (root i) (p.flip (cor
oot i)))) (Set.range ⇑root)                                 (Set.range ⇑root)) →
                             (∀ (i : ι), (p (root i)) (coroot i) = 2) → ι ≃ ι
参数：p : M →ₗ[R] N →ₗ[R] R；root : ι ↪ M；coroot : ι ↪ N；∀ (i : ι),                 
              Set.MapsTo (⇑(Module.preReflection (root i) (p.flip (coroot i)))) 
(Set.range ⇑root)                                 (Set.range ⇑root)；∀ (i : ι), (
p (root i)) (coroot i) = 2。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Basic.0.RootPairing.exist_eq_r
eflection_of_mapsTo`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_
4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] 
[…
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Basic.0.RootPairing.choose_cho
ose_eq_of_mapsTo`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} 
[inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] […

--- 原说明 ---
The bijection on the indexing set induced by reflection.
-/
protected def equiv_of_mapsTo :
    ι ≃ ι where
  toFun j := (exist_eq_reflection_of_mapsTo p root coroot i j h).choose
  invFun j := (exist_eq_reflection_of_mapsTo p root coroot i j h).choose
  left_inv j := choose_choose_eq_of_mapsTo p root coroot i j h hp
  right_inv j := choose_choose_eq_of_mapsTo p root coroot i j h hp

end reflectionPerm

variable (P : RootPairing ι R M N) [Finite ι]

/-- Even though the roots may not span, coroots are distinguished by their pairing with the
roots. The proof depends crucially on the fact that there are finitely-many roots.

Modulo trivial generalisations, this statement is exactly Lemma 1.1.4 on page 87 of SGA 3 XXI. -/
/-
**RootPairing.injOn_dualMap_subtype_span_root_coroot** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing`。
形式化陈述：injOn_dualMap_subtype_span_root_coroot [IsAddTorsionFree M] : InjOn ((span
 R (range P.root)).subtype.dualMap ∘ₗ P.toLinearMap.flip) (range P.coroot)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Module.injOn_dualMap_subtype_span_range_range`：injOn_dualMap_subtype_spa
n_range_range {ι : Type*} [IsAddTorsionFree M] {r : ι ↪ M} {c : ι -> Dual R M} (
hfin : (range r).Finite) (h_two : f…
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `RootPairing.root_coroot_two`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u
_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _ro
ot_.Module R M] […
· 使用定理 `RootPairing.mapsTo_reflection_root`：mapsTo_reflection_root : MapsTo (P.r
eflection i) (range P.root) (range P.root)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f

--- 原说明 ---
Even though the roots may not span, coroots are distinguished by their pairing w
ith the
roots. The proof depends crucially on the fact that there are finitely-many root
s.

Modulo trivial generalisations, this statement is exactly Lemma 1.1.4 on page 87
 of SGA 3 XXI.
-/
lemma injOn_dualMap_subtype_span_root_coroot [IsAddTorsionFree M] :
    InjOn ((span R (range P.root)).subtype.dualMap ∘ₗ P.toLinearMap.flip) (range P.coroot) := by
  have := injOn_dualMap_subtype_span_range_range (finite_range P.root)
    (c := P.toLinearMap.flip ∘ P.coroot) P.root_coroot_two P.mapsTo_reflection_root
  rintro - ⟨i, rfl⟩ - ⟨j, rfl⟩ hij
  exact P.flip.toPerfPair.injective <| this (mem_range_self i) (mem_range_self j) hij

/-- In characteristic zero if there is no torsion, the correspondence between roots and coroots is
unique.

Formally, the point is that the hypothesis `hc` depends only on the range of the coroot mappings. -/
@[ext]
/-
**RootPairing.ext** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] [Finite ι] [CharZero R]   [IsDomain R] [
Module.IsTorsionFree R M] {P₁ P₂ : RootPairing ι R M N},   P₁.toLinearMap = P₂.t
oLinearMap → P₁.root = P₂.root → Set.range ⇑P₁.coroot = Set.range ⇑P₂.coroot → P
₁ = P₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用引理 `RootPairing.injOn_dualMap_subtype_span_root_coroot`：injOn_dualMap_subtyp
e_span_root_coroot [IsAddTorsionFree M] : InjOn ((span R (range P.root)).subtype
.dualMap ∘ₗ P.toLinearMap.flip) (range P…
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Dual.eq_of_preReflection_mapsTo'`：∀ {R : Type u_1} {M : Type u_2}
 [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [Cha
rZero R]   [IsDomain R] [Modu…
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用引理 `RootPairing.coroot_root_two`：coroot_root_two : P.toLinearMap.flip (P.cor
oot i) (P.root i) = 2
· 使用定理 `RootPairing.mapsTo_reflection_root`：mapsTo_reflection_root : MapsTo (P.r
eflection i) (range P.root) (range P.root)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RootPairing.mk.congr_simp`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3
} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root
_.Module R M] […

--- 原说明 ---
In characteristic zero if there is no torsion, the correspondence between roots 
and coroots is
unique.

Formally, the point is that the hypothesis `hc` depends only on the range of the
 coroot mappings.
-/
protected lemma ext [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {P₁ P₂ : RootPairing ι R M N}
    (he : P₁.toLinearMap = P₂.toLinearMap)
    (hr : P₁.root = P₂.root)
    (hc : range P₁.coroot = range P₂.coroot) :
    P₁ = P₂ := by
  have hp (hc' : P₁.coroot = P₂.coroot) : P₁.reflectionPerm = P₂.reflectionPerm := by
    ext i j
    refine P₁.root.injective ?_
    conv_rhs => rw [hr]
    simp only [root_reflectionPerm, reflection_apply, coroot']
    simp only [hr, he, hc']
  suffices P₁.coroot = P₂.coroot by
    obtain ⟨p₁⟩ := P₁; obtain ⟨p₂⟩ := P₂
    #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
    (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
    It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
    canonicalizer; a minimization would help. The original proof was: `grind` -/
    simp_all
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  ext i
  apply P₁.injOn_dualMap_subtype_span_root_coroot (mem_range_self i) (hc ▸ mem_range_self i)
  simp only [LinearMap.coe_comp, comp_apply]
  apply Dual.eq_of_preReflection_mapsTo' (finite_range P₁.root)
  · exact Submodule.subset_span (mem_range_self i)
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_reflection_root i
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · exact hr ▸ he ▸ P₂.mapsTo_reflection_root i
/-
**RootPairing.coroot_eq_coreflection_of_root_eq'** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma coroot_eq_coreflection_of_root_eq' [CharZero R] [IsDomain R] [IsTorsionFree R M]
    (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair]
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, p (root i) (coroot i) = 2)
    (hr : ∀ i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
    (hc : ∀ i, MapsTo (preReflection (coroot i) (p (root i))) (range coroot) (range coroot))
    {i j k : ι} (hk : root k = preReflection (root i) (p.flip (coroot i)) (root j)) :
    coroot k = preReflection (coroot i) (p (root i)) (coroot j) := by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.flip α')
  set sβ := preReflection β (p.flip β')
  let sα' := preReflection α' (p α)
  have hij : preReflection (sα β) (p.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.flip (coroot i)) (root i) = 2 := by simp [hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.flip β') hpi,
      preReflection_apply]
  obtain ⟨l, hl⟩ := hc i (mem_range_self j)
  rw [← hl]
  have hkl : (p.flip (coroot l)) (root k) = 2 := by
    simp only [hl, preReflection_apply, map_sub, map_smul, hk, LinearMap.flip_apply,
      LinearMap.sub_apply, hp j, LinearMap.smul_apply, smul_eq_mul, hp i, mul_two,
      sub_add_cancel_right, mul_neg, sub_neg_eq_add, sα, α, α', β]
    rw [mul_comm (p (root i) (coroot j))]
    abel
  suffices p.flip (coroot k) = p.flip (coroot l) from p.flip.toPerfPair.injective this
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  have := injOn_dualMap_subtype_span_range_range (finite_range root)
    (c := p.flip ∘ coroot) hp hr
  apply this (mem_range_self k) (mem_range_self l)
  refine Dual.eq_of_preReflection_mapsTo' (finite_range root)
    (Submodule.subset_span <| mem_range_self k) (hp k) (hr k) hkl ?_
  rw [comp_apply, hl, hk, hij]
  exact (hr i).comp <| (hr j).comp (hr i)

set_option backward.isDefEq.respectTransparency false in
/-- In characteristic zero if there is no torsion, to check that two finite families of roots and
coroots form a root pairing, it is sufficient to check that they are stable under reflections. -/
/-
**RootPairing.mk'** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：mk' [CharZero R] [IsDomain R] [IsTorsionFree R M] (p : M ->ₗ[R] N ->ₗ[R] R
) [p.IsPerfPair] (root : ι ↪ M) (coroot : ι ↪ N) (hp : forall i, p (root i) (cor
oot i) = 2) (hr : forall i, MapsTo (preReflection (root i) (p.flip (coroot i))) 
(range root) (range root)) (hc : forall i, MapsTo (preReflection (coroot i) (p (
root i))) (range coroot) (range coroot)) : RootPairing ι R M N where toLinearMap
参数：p : M ->ₗ[R] N ->ₗ[R] R；root : ι ↪ M；coroot : ι ↪ N；hp : forall i, p (root i)
 (coroot i) = 2；hr : forall i, MapsTo (preReflection (root i) (p.flip (coroot i)
)) (range root) (range root)；hc : forall i, MapsTo (preReflection (coroot i) (p 
(root i))) (range coroot) (range coroot)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In characteristic zero if there is no torsion, to check that two finite families
 of roots and
coroots form a root pairing, it is sufficient to check that they are stable unde
r reflections.
-/
def mk' [CharZero R] [IsDomain R] [IsTorsionFree R M]
    (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair]
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, p (root i) (coroot i) = 2)
    (hr : ∀ i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
    (hc : ∀ i, MapsTo (preReflection (coroot i) (p (root i))) (range coroot) (range coroot)) :
    RootPairing ι R M N where
  toLinearMap := p
  root := root
  coroot := coroot
  root_coroot_two := hp
  reflectionPerm i := RootPairing.equiv_of_mapsTo p root coroot i hr hp
  reflectionPerm_root i j := by
    simp [(exist_eq_reflection_of_mapsTo p root coroot i j hr).choose_spec, preReflection_apply]
  reflectionPerm_coroot i j := by
    refine (coroot_eq_coreflection_of_root_eq' p root coroot hp hr hc ?_).symm
    rw [equiv_of_mapsTo_apply, (exist_eq_reflection_of_mapsTo p root coroot i j hr).choose_spec]

variable [P.IsRootSystem]

/-- In characteristic zero if there is no torsion, a finite root system is determined entirely by
its roots. -/
/-
**RootPairing.IsRootSystem.ext** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.IsRootSyst
em`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] [Finite ι] [CharZero R]   [IsDomain R] [
Module.IsTorsionFree R M] {P₁ P₂ : RootPairing ι R M N} [P₁.IsRootSystem] [P₂.Is
RootSystem],   P₁.toLinearMap = P₂.toLinearMap → P₁.root = P₂.root → P₁ = P₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Module.Dual.eq_of_preReflection_mapsTo`：∀ {R : Type u_1} {M : Type u_2} 
[inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [Char
Zero R]   [IsDomain R] [Modu…
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `RootPairing.IsRootSystem.span_root_eq_top`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}  
 {inst_2 : _root_.Module R M} {…
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.coroot_root_two`：coroot_root_two : P.toLinearMap.flip (P.cor
oot i) (P.root i) = 2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.flip.instIsPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : Type
 u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   
[inst_3 : _root_.Mo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.toPerfPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} {N : Ty
pe u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R] 
  [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.mapsTo_reflection_root`：mapsTo_reflection_root : MapsTo (P.r
eflection i) (range P.root) (range P.root)
· 使用定理 `RootPairing.ext`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Typ
e u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R
 M] […
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b

--- 原说明 ---
In characteristic zero if there is no torsion, a finite root system is determine
d entirely by
its roots.
-/
protected lemma IsRootSystem.ext [CharZero R] [IsDomain R] [IsTorsionFree R M]
    {P₁ P₂ : RootPairing ι R M N} [P₁.IsRootSystem] [P₂.IsRootSystem]
    (he : P₁.toLinearMap = P₂.toLinearMap)
    (hr : P₁.root = P₂.root) :
    P₁ = P₂ := by
  suffices ∀ (P₁ P₂ : RootPairing ι R M N) [P₁.IsRootSystem] [P₂.IsRootSystem],
      P₁.toLinearMap = P₂.toLinearMap → P₁.root = P₂.root → range P₁.coroot ⊆ range P₂.coroot by
    have h₁ := this P₁ P₂ he hr
    have h₂ := this P₂ P₁ he.symm hr.symm
    exact RootPairing.ext he hr (le_antisymm h₁ h₂)
  clear! P₁ P₂
  rintro P₁ P₂ hP₁ hP₂ he hr - ⟨i, rfl⟩
  use i
  apply P₁.flip.toPerfPair.injective
  apply Dual.eq_of_preReflection_mapsTo (finite_range P₁.root) IsRootSystem.span_root_eq_top
  · exact hr ▸ he ▸ P₂.coroot_root_two i
  · change MapsTo (preReflection _ (P₁.toLinearMap.flip.toPerfPair _)) _ _
    simp_rw [hr, he]
    exact P₂.mapsTo_reflection_root i
  · exact P₁.coroot_root_two i
  · exact P₁.mapsTo_reflection_root i
/-
**RootPairing.coroot_eq_coreflection_of_root_eq_of_span_eq_top** 是 Mathlib 中的一个引
理，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma coroot_eq_coreflection_of_root_eq_of_span_eq_top [CharZero R] [IsDomain R]
    [IsTorsionFree R M] (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair]
    (root : ι ↪ M)
    (coroot : ι ↪ N)
    (hp : ∀ i, p (root i) (coroot i) = 2)
    (hs : ∀ i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
    (hsp : span R (range root) = ⊤)
    {i j k : ι} (hk : root k = preReflection (root i) (p.flip (coroot i)) (root j)) :
    coroot k = preReflection (coroot i) (p (root i)) (coroot j) := by
  set α := root i
  set β := root j
  set α' := coroot i
  set β' := coroot j
  set sα := preReflection α (p.flip α')
  set sβ := preReflection β (p.flip β')
  let sα' := preReflection α' (p α)
  have hij : preReflection (sα β) (p.flip (sα' β')) = sα ∘ₗ sβ ∘ₗ sα := by
    ext
    have hpi : (p.flip (coroot i)) (root i) = 2 := by simp [hp i]
    simp [α, β, α', β', sα, sβ, sα', ← preReflection_preReflection β (p.flip β') hpi,
      preReflection_apply] -- v4.7.0-rc1 issues
  apply p.flip.toPerfPair.injective
  apply Dual.eq_of_preReflection_mapsTo (finite_range root) hsp (hp k) (hs k)
  · simp [map_sub, α, β, α', β', sα, hk, preReflection_apply, hp i, hp j,
      mul_comm (p α β')]
    ring -- v4.7.0-rc1 issues
  · rw [hk, LinearMap.toLinearMap_toPerfPair, hij]
    exact (hs i).comp <| (hs j).comp (hs i)

section

variable {k : Type*} [Field k] [CharZero k] [Module k M] [Module k N]
  (p : M →ₗ[k] N →ₗ[k] k) [p.IsPerfPair]
  (root : ι ↪ M)
  (coroot : ι ↪ N)
  (hp : ∀ i, p (root i) (coroot i) = 2)
  (hs : ∀ i, MapsTo (preReflection (root i) (p.flip (coroot i))) (range root) (range root))
  (hsp : span k (range root) = ⊤)

/-- Over a field of characteristic zero, to check that a finite family of roots form a
crystallographic root system, we do not need to check that the coroots are stable under reflections
since this follows from the corresponding property for the roots. Likewise, we do not need to
check that the coroots span. -/
/-
**RootPairing.mk''** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：mk'' : RootPairing ι k M N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Over a field of characteristic zero, to check that a finite family of roots form
 a
crystallographic root system, we do not need to check that the coroots are stabl
e under reflections
since this follows from the corresponding property for the roots. Likewise, we d
o not need to
check that the coroots span.
-/
def mk'' :
    RootPairing ι k M N :=
  .mk' p root coroot hp hs <| by
    rintro i - ⟨j, rfl⟩
    use RootPairing.equiv_of_mapsTo p root coroot i hs hp j
    refine (coroot_eq_coreflection_of_root_eq_of_span_eq_top p root coroot hp hs hsp ?_)
    rw [equiv_of_mapsTo_apply, (exist_eq_reflection_of_mapsTo p root coroot i j hs).choose_spec]

variable {p root coroot hp hs hsp} in
/-
**RootPairing.isRootSystem_mk''** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：isRootSystem_mk'' (h_int : forall i j, exists z : Int, z = p (root i) (cor
oot j)) : (mk'' p root coroot hp hs hsp).IsRootSystem where span_root_eq_top
参数：h_int : forall i j, exists z : Int, z = p (root i) (coroot j)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RootPairing.rootSpan_eq_top_iff`：rootSpan_eq_top_iff : P.rootSpan R = ⊤ 
↔ P.corootSpan R = ⊤
-/
lemma isRootSystem_mk'' (h_int : ∀ i j, ∃ z : ℤ, z = p (root i) (coroot j)) :
    (mk'' p root coroot hp hs hsp).IsRootSystem where
  span_root_eq_top := hsp
  span_coroot_eq_top :=
    have _i : (mk'' p root coroot hp hs hsp).IsCrystallographic := ⟨h_int⟩
    have _i : Fintype ι := Fintype.ofFinite ι
    (rootSpan_eq_top_iff _).mp hsp

end

end RootPairing

