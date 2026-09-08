/-
Copyright (c) 2025 Hang Lu Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Fabrizio Barroero, Stefano Francaviglia,
  Francesco Milizia, Valerio Proietti, Hang Lu Su, Lawrence Wu, Javier Gómez Zaragoza
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.Schreier
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finite.Sum
public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finitely Presented Groups

This file defines finitely presented groups.

## Main definitions
* `Subgroup.IsFinitelyNormallyGenerated N`: says that the subgroup `N` is the normal closure of a
  finite set.
* `IsFinitelyPresented`: defines when a group is finitely presented.

## Main results
* `Subgroup.IsFinitelyNormallyGenerated.map`: Being the normal closure of a finite set is preserved
under surjective homomorphism.
* `IsFinitelyPresented.equiv`: finitely presented groups are closed under isomorphism.

## Tags
finitely presented group, finitely generated normal closure
-/

@[expose] public section

variable {G H α β : Type*} [Group G] [Group H]

/-- `N.IsFinitelyNormallyGenerated` says that the subgroup `N` is the normal closure
 of a finite set. -/
@[to_additive /-- `N.IsFinitelyNormallyGenerated` says that the additive subgroup `N`
is the normal closure of a finite set. -/]
/-
**Subgroup.IsFinitelyNormallyGenerated** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subgroup.IsFinitelyNormallyGenerated (N : Subgroup G) : Prop
参数：N : Subgroup G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Subgroup.IsFinitelyNormallyGenerated (N : Subgroup G) : Prop :=
  ∃ S : Set G, S.Finite ∧ Subgroup.normalClosure S = N

@[deprecated (since := "2026-06-25")]
alias Subgroup.IsNormalClosureFG := Subgroup.IsFinitelyNormallyGenerated

namespace Subgroup.IsFinitelyNormallyGenerated

/-- Being the normal closure of a finite set is invariant under surjective homomorphism. -/
@[to_additive /-- Being the additive normal closure of a finite set is invariant under
surjective homomorphism. -/]
/-
**Subgroup.IsFinitelyNormallyGenerated.map** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.I
sFinitelyNormallyGenerated`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {N : S
ubgroup G},   N.IsFinitelyNormallyGenerated →     ∀ {f : G →* H}, Function.Surje
ctive ⇑f → (Subgroup.map f N).IsFinitelyNormallyGenerated
参数：Subgroup.map f N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.map_normalClosure`：map_normalClosure (s : Set G) (f : G ->* N) 
(hf : Surjective f) : (normalClosure s).map f = normalClosure (f '' s)
-/
protected theorem map {N : Subgroup G} (hN : N.IsFinitelyNormallyGenerated)
    {f : G →* H} (hf : Function.Surjective f) : (N.map f).IsFinitelyNormallyGenerated := by
  obtain ⟨S, hSfinite, hSclosure⟩ := hN
  refine ⟨f '' S, hSfinite.image _, ?_⟩
  rw [← hSclosure, Subgroup.map_normalClosure _ _ hf]

@[to_additive]
/-
**Subgroup.IsFinitelyNormallyGenerated.of_FG** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
.IsFinitelyNormallyGenerated`。
形式化陈述：of_FG (N : Subgroup G) [N.Normal] [h : Group.FG N] : N.IsFinitelyNormallyG
enerated
参数：N : Subgroup G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.fg_iff`：Subgroup.fg_iff (P : Subgroup G) : Subgroup.FG P ↔ exis
ts S : Set G, Subgroup.closure S = P ∧ S.Finite
· 使用定理 `Group.fg_iff_subgroup_fg`：Group.fg_iff_subgroup_fg (H : Subgroup G) : Gr
oup.FG H ↔ H.FG
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subgroup.normalClosure_le_normal`：normalClosure_le_normal {N : Subgroup 
G} [N.Normal] (h : s subseteq N) : normalClosure s <= N
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Subgroup.closure_le_normalClosure`：closure_le_normalClosure {s : Set G} 
: closure s <= normalClosure s
-/
theorem of_FG (N : Subgroup G) [N.Normal] [h : Group.FG N] : N.IsFinitelyNormallyGenerated := by
  obtain ⟨S, rfl, hS⟩ := N.fg_iff.mp ((Group.fg_iff_subgroup_fg N).mp h)
  exact ⟨S, hS, le_antisymm (normalClosure_le_normal subset_closure) closure_le_normalClosure⟩

open Function Set Subgroup in
/-- The preimage of a finitely generated normal subgroup by a surjective homomorphism with
a finitely generated kernel is finitely generated. -/
@[to_additive /-- The preimage of a finitely generated normal subgroup by a surjective additive
homomorphism with a finitely generated kernel is finitely generated. -/]
/-
**Subgroup.IsFinitelyNormallyGenerated.comap** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup
.IsFinitelyNormallyGenerated`。
形式化陈述：∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H] {N : S
ubgroup H},   N.IsFinitelyNormallyGenerated →     ∀ {f : G →* H},       Function
.Surjective ⇑f → f.ker.IsFinitelyNormallyGenerated → (Subgroup.comap f N).IsFini
telyNormallyGenerated
参数：Subgroup.comap f N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用引理 `Function.comp_surjInv`：comp_surjInv (hf : f.Surjective) : f ∘ f.surjInv 
hf = id
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `Subgroup.map_normalClosure`：map_normalClosure (s : Set G) (f : G ->* N) 
(hf : Surjective f) : (normalClosure s).map f = normalClosure (f '' s)
· 使用定理 `Subgroup.comap_map_eq`：comap_map_eq (H : Subgroup G) : comap f (map f H)
 = H ⊔ f.ker
· 使用定理 `Subgroup.normalClosure_union`：normalClosure_union {G : Type*} [Group G] 
(s t : Set G) : normalClosure (s union t) = normalClosure s ⊔ normalClosure t
-/
protected theorem comap {N : Subgroup H} (hN : N.IsFinitelyNormallyGenerated)
    {f : G →* H} (hf : Surjective f) (hf' : f.ker.IsFinitelyNormallyGenerated) :
    (N.comap f).IsFinitelyNormallyGenerated := by
  obtain ⟨S, hS_fin, hS⟩ := hN
  obtain ⟨T, hT_fin, hT⟩ := hf'
  have : ∃ S', S'.Finite ∧ f '' S' = S :=
    ⟨surjInv hf '' S, hS_fin.image _, by rw [← image_comp, comp_surjInv, image_id]⟩
  clear hS_fin
  obtain ⟨S, hS_fin, rfl⟩ := this
  refine ⟨S ∪ T, hS_fin.union hT_fin, ?_⟩
  rw [← hS, ← map_normalClosure S f hf, comap_map_eq, ← hT, normalClosure_union]

/-- The trivial group is the normal closure of a finite set of relations. -/
@[to_additive /-- The trivial additive group is the normal closure of a finite set of relations. -/]
/-
**Subgroup.IsFinitelyNormallyGenerated.bot** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup.I
sFinitelyNormallyGenerated`。
形式化陈述：∀ {G : Type u_1} [inst : Group G], ⊥.IsFinitelyNormallyGenerated
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.IsFinitelyNormallyGenerated.of_FG`：of_FG (N : Subgroup G) [N.No
rmal] [h : Group.FG N] : N.IsFinitelyNormallyGenerated
· 使用定理 `Group.fg_of_finite`：∀ {G : Type u_3} [inst : Group G] [Finite G], Group.
FG G
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
The trivial group is the normal closure of a finite set of relations.
-/
protected theorem bot : (⊥ : Subgroup G).IsFinitelyNormallyGenerated := of_FG _

end Subgroup.IsFinitelyNormallyGenerated

/-- An additive group is finitely presented if it has a finite generating set such that the kernel
of the induced map from the free additive group on that set is the normal closure
of finitely many relations. -/
/-
**AddGroup.IsFinitelyPresented** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddGroup`。
形式化陈述：(G : Type u_5) → [AddGroup G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An additive group is finitely presented if it has a finite generating set such t
hat the kernel
of the induced map from the free additive group on that set is the normal closur
e
of finitely many relations.
-/
class AddGroup.IsFinitelyPresented (G : Type*) [AddGroup G] : Prop where
  out : ∃ (n : ℕ) (φ : FreeAddGroup (Fin n) →+ G),
  Function.Surjective φ ∧ φ.ker.IsFinitelyNormallyGenerated

/-- A group is finitely presented if it has a finite generating set such that the kernel
of the induced map from the free group on that set is the normal closure of finitely many
relations. -/
@[mk_iff, to_additive existing]
/-
**Group.IsFinitelyPresented** 是 Mathlib 中的一个归纳类型，位于命名空间 `Group`。
形式化陈述：(G : Type u_5) → [Group G] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A group is finitely presented if it has a finite generating set such that the ke
rnel
of the induced map from the free group on that set is the normal closure of fini
tely many
relations.
-/
class Group.IsFinitelyPresented (G : Type*) [Group G] : Prop where
  out : ∃ (n : ℕ) (φ : FreeGroup (Fin n) →* G),
  Function.Surjective φ ∧ φ.ker.IsFinitelyNormallyGenerated

namespace Group.IsFinitelyPresented

/-- Finitely presented groups are closed under isomorphism. -/
@[to_additive /-- Finitely presented additive groups are closed under additive isomorphism. -/
]
/-
**Group.IsFinitelyPresented.equiv** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsFinitelyPre
sented`。
形式化陈述：equiv (iso : G ≃* H) [h : IsFinitelyPresented G] : IsFinitelyPresented H
参数：iso : G ≃* H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `MulEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [ins
t_1 : Mul N] (e : M ≃* N), Function.Surjective ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidHom.ker_mulEquiv_comp`：ker_mulEquiv_comp {P : Type*} [MulOneClass 
P] (f : G ->* N) (iso : N ≃* P) : ((iso : N ->* P).comp f).ker = f.ker
-/
theorem equiv (iso : G ≃* H) [h : IsFinitelyPresented G] : IsFinitelyPresented H := by
  obtain ⟨n, φ, hφsurj, hNC⟩ := h
  refine ⟨n, (iso : G →* H).comp φ, iso.surjective.comp hφsurj, ?_⟩
  rwa [φ.ker_mulEquiv_comp iso]

/-- The image of a finitely presented group under a surjective homomorphism whose kernel is
finitely generated as a normal subgroup is finitely presented. -/
@[to_additive /-- The image of a finitely presented additive group under a surjective additive
homomorphism whose kernel is finitely generated as a normal subgroup is finitely presented. -/]
/-
**Group.IsFinitelyPresented.of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsFin
itelyPresented`。
形式化陈述：of_surjective [hG : IsFinitelyPresented G] (f : G ->* H) (hf_surj : Functi
on.Surjective f) (hf_ker : f.ker.IsFinitelyNormallyGenerated) : IsFinitelyPresen
ted H
参数：f : G ->* H；hf_surj : Function.Surjective f；hf_ker : f.ker.IsFinitelyNormally
Generated。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.IsFinitelyPresented.out`：∀ {G : Type u_5} {inst : Group G} [self :
 Group.IsFinitelyPresented G],   ∃ n φ, Function.Surjective ⇑φ ∧ φ.ker.IsFinitel
yNormallyGenerated
· 使用定理 `Function.Surjective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3}
 {g : β → γ} {f : α → β},   Function.Surjective g → Function.Surjective f → Func
tion.Surjectiv…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.comap_ker`：comap_ker {P : Type*} [MulOneClass P] (g : N ->* P)
 (f : G ->* N) : g.ker.comap f = (g.comp f).ker
· 使用定理 `Subgroup.IsFinitelyNormallyGenerated.comap`：∀ {G : Type u_1} {H : Type u
_2} [inst : Group G] [inst_1 : Group H] {N : Subgroup H},   N.IsFinitelyNormally
Generated →     ∀ {f : G →* H}, …
-/
theorem of_surjective [hG : IsFinitelyPresented G] (f : G →* H)
    (hf_surj : Function.Surjective f) (hf_ker : f.ker.IsFinitelyNormallyGenerated) :
    IsFinitelyPresented H := by
  obtain ⟨n, φ, hφ_surj, hφ_ker⟩ := hG.out
  refine ⟨n, f.comp φ, hf_surj.comp hφ_surj, ?_⟩
  rw [← MonoidHom.comap_ker]
  exact hf_ker.comap hφ_surj hφ_ker

/-- The quotient of a finitely presented group by a subgroup
which is finitely generated as a normal subgroup is finitely presented. -/
@[to_additive /-- The quotient of a finitely presented additive group by an additive subgroup
which is finitely generated as a normal subgroup is finitely presented. -/]
/-
**Group.IsFinitelyPresented.quotient** 是 Mathlib 中的一个定理，位于命名空间 `Group.IsFinitely
Presented`。
形式化陈述：quotient [hG : IsFinitelyPresented G] (N : Subgroup G) [N.Normal] (hN : N.
IsFinitelyNormallyGenerated) : IsFinitelyPresented (G ⧸ N)
参数：N : Subgroup G；hN : N.IsFinitelyNormallyGenerated。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Group.IsFinitelyPresented.of_surjective`：of_surjective [hG : IsFinitelyP
resented G] (f : G ->* H) (hf_surj : Function.Surjective f) (hf_ker : f.ker.IsFi
nitelyNormallyGenerated) : Is…
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
-/
theorem quotient [hG : IsFinitelyPresented G] (N : Subgroup G) [N.Normal]
    (hN : N.IsFinitelyNormallyGenerated) : IsFinitelyPresented (G ⧸ N) :=
  of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    ((QuotientGroup.ker_mk' N).symm ▸ hN)

open QuotientGroup in
/-
**Group.IsFinitelyPresented.exists_mulEquiv_presentedGroup** 是 Mathlib 中的一个定理，位于
命名空间 `Group.IsFinitelyPresented`。
形式化陈述：exists_mulEquiv_presentedGroup [hg : IsFinitelyPresented G] : exists n : N
at, exists s : Set (FreeGroup (Fin n)), Set.Finite s ∧ Nonempty (G ≃* PresentedG
roup s)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_mulEquiv_presentedGroup [hg : IsFinitelyPresented G] :
    ∃ n : ℕ, ∃ s : Set (FreeGroup (Fin n)), Set.Finite s ∧ Nonempty (G ≃* PresentedGroup s) := by
  obtain ⟨n, φ, hφ, s, hs, hsφ⟩ := hg
  exact ⟨n, s, hs, ⟨(quotientKerEquivOfSurjective φ hφ).symm.trans (quotientMulEquivOfEq hsφ.symm)⟩⟩

/-- A free group with a finite number of generators is finitely presented. -/
@[to_additive /-- A free additive group with a finite number of generators is finitely presented. -/
]
/-
**Group.IsFinitelyPresented.** 是 Mathlib 中的一个实例，位于命名空间 `Group.IsFinitelyPresente
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] : IsFinitelyPresented (FreeGroup α) := by
  have ⟨n, _, f, hf_surj, hf_inj⟩ := Finite.exists_equiv_fin α
  refine ⟨n, FreeGroup.map f, FreeGroup.map_surjective hf_surj.surjective, ?_⟩
  · rw [(FreeGroup.map f).ker_eq_bot (FreeGroup.map_injective hf_inj.injective)]
    exact .bot
/-
**Group.IsFinitelyPresented.** 是 Mathlib 中的一个实例，位于命名空间 `Group.IsFinitelyPresente
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Finite α] (s : Set (FreeGroup α)) [Finite s] :
    IsFinitelyPresented (PresentedGroup s) :=
  of_surjective (PresentedGroup.mk s) (PresentedGroup.mk_surjective s)
    ⟨s, ‹_›, (QuotientGroup.ker_mk' (Subgroup.normalClosure s)).symm⟩

/-- `Multiplicative ℤ` is finitely presented. -/
/-
**Group.IsFinitelyPresented.** 是 Mathlib 中的一个实例，位于命名空间 `Group.IsFinitelyPresente
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiplicative ℤ` is finitely presented.
-/
instance : IsFinitelyPresented (Multiplicative ℤ) :=
  equiv (FreeGroup.mulEquivIntOfUnique : FreeGroup Unit ≃* Multiplicative ℤ)

/-- ℤ is finitely presented -/
/-
**Group.IsFinitelyPresented.** 是 Mathlib 中的一个实例，位于命名空间 `Group.IsFinitelyPresente
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
ℤ is finitely presented
-/
instance : AddGroup.IsFinitelyPresented ℤ :=
  AddGroup.IsFinitelyPresented.equiv (FreeAddGroup.addEquivIntOfUnique : FreeAddGroup Unit ≃+ ℤ)

/-- The free product of finitely presented groups is finitely presented -/
/-
**Group.IsFinitelyPresented.** 是 Mathlib 中的一个实例，位于命名空间 `Group.IsFinitelyPresente
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free product of finitely presented groups is finitely presented
-/
instance [IsFinitelyPresented G] [IsFinitelyPresented H] :
    IsFinitelyPresented (Monoid.Coprod G H) := by
  obtain ⟨_, sG, ⟨_ : Finite sG, ⟨φG⟩⟩⟩ := exists_mulEquiv_presentedGroup (G := G)
  obtain ⟨_, sH, ⟨_ : Finite sH, ⟨φH⟩⟩⟩ := exists_mulEquiv_presentedGroup (G := H)
  exact equiv ((PresentedGroup.coprodPresentations sG sH).trans (MulEquiv.coprodCongr φG φH).symm)

variable (G)

/-- Any finite group is finitely presented. -/
@[to_additive]
/-
**Group.IsFinitelyPresented.** 是 Mathlib 中的一个实例，位于命名空间 `Group.IsFinitelyPresente
d`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any finite group is finitely presented.
-/
instance [Finite G] : IsFinitelyPresented G :=
  of_surjective FreeGroup.prod FreeGroup.prod_surjective (.of_FG FreeGroup.prod.ker)

end Group.IsFinitelyPresented

