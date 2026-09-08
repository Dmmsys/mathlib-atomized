/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Order.CompleteSublattice
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Isotypic modules and isotypic components

## Main definitions

* `IsIsotypicOfType R M S` means that all simple submodules of the `R`-module `M`
  are isomorphic to `S`. Such a module `M` is isomorphic to a finsupp over `S`,
  see `IsIsotypicOfType.linearEquiv_finsupp`.

* `IsIsotypic R M` means that all simple submodules of the `R`-module `M`
  are isomorphic to each other.

* `isotypicComponent R M S` is the sum of all submodules of `M` isomorphic to `S`.

* `isotypicComponents R M` is the set of all nontrivial isotypic components of `M`
  (where `S` is taken to be simple submodules).

* `Submodule.IsFullyInvariant N` means that the submodule `N` of an `R`-module `M` is mapped into
  itself by all endomorphisms of `M`. The `fullyInvariantSubmodule`s of `M` form a complete
  lattice, which is atomic if `M` is semisimple, in which case the atoms are the isotypic
  components of `M`. A fully invariant submodule of a semiring as a module over itself
  is simply a two-sided ideal, see `isFullyInvariant_iff_isTwoSided`.

* `iSupIndep.ringEquiv`, `iSupIndep.algEquiv`: if `M` is the direct sum of fully invariant
  submodules `Nᵢ`, then `End R M` is isomorphic to `Πᵢ End R Nᵢ`. This can be applied to
  the isotypic components of a semisimple module `M`, yielding `IsSemisimpleModule.endAlgEquiv`.

## Keywords

isotypic component, fully invariant submodule

-/

@[expose] public section

universe u

variable (R₀ R : Type*) (M : Type u) (N S : Type*) [CommSemiring R₀]
  [Ring R] [Algebra R₀ R] [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup S] [Module R M] [Module R N] [Module R S]

/-- An `R`-module `M` is isotypic of type `S` if all simple submodules of `M` are isomorphic
to `S`. If `M` is semisimple, it is equivalent to requiring that all simple quotients of `M` are
isomorphic to `S`. -/
/-
**IsIsotypicOfType** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsIsotypicOfType : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-module `M` is isotypic of type `S` if all simple submodules of `M` are is
omorphic
to `S`. If `M` is semisimple, it is equivalent to requiring that all simple quot
ients of `M` are
isomorphic to `S`.
-/
def IsIsotypicOfType : Prop := ∀ (m : Submodule R M) [IsSimpleModule R m], Nonempty (m ≃ₗ[R] S)

/-- An `R`-module `M` is isotypic if all its simple submodules are isomorphic. -/
/-
**IsIsotypic** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsIsotypic : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-module `M` is isotypic if all its simple submodules are isomorphic.
-/
def IsIsotypic : Prop := ∀ (m : Submodule R M) [IsSimpleModule R m], IsIsotypicOfType R M m

variable {R M S} in
/-
**IsIsotypicOfType.isIsotypic** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypicOfType.isIsotypic (h : IsIsotypicOfType R M S) : IsIsotypic R M
参数：h : IsIsotypicOfType R M S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsIsotypicOfType.isIsotypic (h : IsIsotypicOfType R M S) : IsIsotypic R M :=
  fun m _ m' _ ↦ ⟨(h m').some.trans (h m).some.symm⟩

@[nontriviality]
/-
**IsIsotypicOfType.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypicOfType.of_subsingleton [Subsingleton M] : IsIsotypicOfType R M S
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleModule.nontrivial`：IsSimpleModule.nontrivial [IsSimpleModule R M
] : Nontrivial M
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `Function.Injective.subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β}, Function.Injective f → ∀ [Subsingleton β], Subsingleton α
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
-/
theorem IsIsotypicOfType.of_subsingleton [Subsingleton M] : IsIsotypicOfType R M S :=
  fun S ↦ have := IsSimpleModule.nontrivial R S
    (not_subsingleton _ S.subtype_injective.subsingleton).elim
/-
**IsIsotypic.of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 `IsIsotypic`。
形式化陈述：∀ (R : Type u_2) (M : Type u) [inst : Ring R] [inst_1 : AddCommGroup M] [i
nst_2 : _root_.Module R M] [Subsingleton M],   IsIsotypic R M
参数：R : Type u_2；M : Type u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypicOfType.isIsotypic`：IsIsotypicOfType.isIsotypic (h : IsIsotypic
OfType R M S) : IsIsotypic R M
· 使用定理 `IsIsotypicOfType.of_subsingleton`：IsIsotypicOfType.of_subsingleton [Subs
ingleton M] : IsIsotypicOfType R M S
-/
@[nontriviality] theorem IsIsotypic.of_subsingleton [Subsingleton M] : IsIsotypic R M :=
  fun S ↦ (IsIsotypicOfType.of_subsingleton R M S).isIsotypic S
/-
**IsIsotypicOfType.of_isSimpleModule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypicOfType.of_isSimpleModule [IsSimpleModule R M] : IsIsotypicOfType
 R M M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAtom_iff_eq_top`：isAtom_iff_eq_top {a : α} : IsAtom a ↔ a = ⊤
· 使用定理 `IsSimpleModule.toIsSimpleOrder`：∀ {R : Type u_2} {inst : Ring R} {M : Ty
pe u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : IsSimpl
eModule R M], IsSimp…
· 使用定理 `isSimpleModule_iff_isAtom`：isSimpleModule_iff_isAtom : IsSimpleModule R 
m ↔ IsAtom m
-/
theorem IsIsotypicOfType.of_isSimpleModule [IsSimpleModule R M] : IsIsotypicOfType R M M :=
  fun S hS ↦ by
    rw [isSimpleModule_iff_isAtom, isAtom_iff_eq_top] at hS
    exact ⟨.trans (.ofEq _ _ hS) Submodule.topEquiv⟩

variable {R}
/-
**IsIsotypic.of_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypic.of_self [IsSemisimpleRing R] (h : IsIsotypic R R) : IsIsotypic 
R M
参数：h : IsIsotypic R R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule`：IsSemisimpl
eRing.exists_linearEquiv_ideal_of_isSimpleModule [IsSemisimpleRing R] [h : IsSim
pleModule R M] : exists I : Ideal R, Nonempty (M …
· 使用定理 `IsSimpleModule.congr`：IsSimpleModule.congr (e : M ≃ₗ[R] N) [IsSimpleModu
le R N] : IsSimpleModule R M where __
-/
theorem IsIsotypic.of_self [IsSemisimpleRing R] (h : IsIsotypic R R) : IsIsotypic R M :=
  fun m _ m' _ ↦
    have ⟨_, ⟨e⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m
    have ⟨_, ⟨e'⟩⟩ := IsSemisimpleRing.exists_linearEquiv_ideal_of_isSimpleModule R m'
    have := IsSimpleModule.congr e.symm
    have := IsSimpleModule.congr e'.symm
    ⟨e'.trans <| (h _ _).some.trans e.symm⟩

variable {M N S}
/-
**IsIsotypicOfType.of_linearEquiv_type** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypicOfType.of_linearEquiv_type (h : IsIsotypicOfType R M S) (e : S ≃
ₗ[R] N) : IsIsotypicOfType R M N
参数：h : IsIsotypicOfType R M S；e : S ≃ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsIsotypicOfType.of_linearEquiv_type (h : IsIsotypicOfType R M S) (e : S ≃ₗ[R] N) :
    IsIsotypicOfType R M N := fun m _ ↦ ⟨(h m).some.trans e⟩
/-
**IsIsotypicOfType.of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypicOfType.of_injective (h : IsIsotypicOfType R N S) (f : M ->ₗ[R] N
) (inj : Function.Injective f) : IsIsotypicOfType R M S
参数：h : IsIsotypicOfType R N S；f : M ->ₗ[R] N；inj : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `IsSimpleModule.congr`：IsSimpleModule.congr (e : M ≃ₗ[R] N) [IsSimpleModu
le R N] : IsSimpleModule R M where __
-/
theorem IsIsotypicOfType.of_injective (h : IsIsotypicOfType R N S) (f : M →ₗ[R] N)
    (inj : Function.Injective f) : IsIsotypicOfType R M S := fun m ↦
  have em := m.equivMapOfInjective f inj
  have := IsSimpleModule.congr em.symm
  ⟨em.trans (h (m.map f)).some⟩
/-
**IsIsotypic.of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypic.of_injective (h : IsIsotypic R N) (f : M ->ₗ[R] N) (inj : Funct
ion.Injective f) : IsIsotypic R M
参数：h : IsIsotypic R N；f : M ->ₗ[R] N；inj : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `IsSimpleModule.congr`：IsSimpleModule.congr (e : M ≃ₗ[R] N) [IsSimpleModu
le R N] : IsSimpleModule R M where __
· 使用定理 `IsIsotypicOfType.of_linearEquiv_type`：IsIsotypicOfType.of_linearEquiv_ty
pe (h : IsIsotypicOfType R M S) (e : S ≃ₗ[R] N) : IsIsotypicOfType R M N
· 使用定理 `IsIsotypicOfType.of_injective`：IsIsotypicOfType.of_injective (h : IsIsot
ypicOfType R N S) (f : M ->ₗ[R] N) (inj : Function.Injective f) : IsIsotypicOfTy
pe R M S
-/
theorem IsIsotypic.of_injective (h : IsIsotypic R N) (f : M →ₗ[R] N) (inj : Function.Injective f) :
    IsIsotypic R M := fun m _ ↦
  have em := (m.equivMapOfInjective f inj).symm
  have := IsSimpleModule.congr em
  ((h (m.map f)).of_injective f inj).of_linearEquiv_type em
/-
**LinearEquiv.isIsotypicOfType_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isIsotypicOfType_iff (e : M ≃ₗ[R] N) : IsIsotypicOfType R M S 
↔ IsIsotypicOfType R N S
参数：e : M ≃ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypicOfType.of_injective`：IsIsotypicOfType.of_injective (h : IsIsot
ypicOfType R N S) (f : M ->ₗ[R] N) (inj : Function.Injective f) : IsIsotypicOfTy
pe R M S
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem LinearEquiv.isIsotypicOfType_iff (e : M ≃ₗ[R] N) :
    IsIsotypicOfType R M S ↔ IsIsotypicOfType R N S :=
  ⟨(·.of_injective _ e.symm.injective), (·.of_injective _ e.injective)⟩
/-
**LinearEquiv.isIsotypicOfType_iff_type** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isIsotypicOfType_iff_type (e : N ≃ₗ[R] S) : IsIsotypicOfType R
 M N ↔ IsIsotypicOfType R M S
参数：e : N ≃ₗ[R] S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypicOfType.of_linearEquiv_type`：IsIsotypicOfType.of_linearEquiv_ty
pe (h : IsIsotypicOfType R M S) (e : S ≃ₗ[R] N) : IsIsotypicOfType R M N
-/
theorem LinearEquiv.isIsotypicOfType_iff_type (e : N ≃ₗ[R] S) :
    IsIsotypicOfType R M N ↔ IsIsotypicOfType R M S :=
  ⟨(·.of_linearEquiv_type e), (·.of_linearEquiv_type e.symm)⟩
/-
**LinearEquiv.isIsotypic_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isIsotypic_iff (e : M ≃ₗ[R] N) : IsIsotypic R M ↔ IsIsotypic R
 N
参数：e : M ≃ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypic.of_injective`：IsIsotypic.of_injective (h : IsIsotypic R N) (f
 : M ->ₗ[R] N) (inj : Function.Injective f) : IsIsotypic R M
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem LinearEquiv.isIsotypic_iff (e : M ≃ₗ[R] N) : IsIsotypic R M ↔ IsIsotypic R N :=
  ⟨(·.of_injective _ e.symm.injective), (·.of_injective _ e.injective)⟩

set_option backward.isDefEq.respectTransparency false in
/-
**isIsotypicOfType_submodule_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIsotypicOfType_submodule_iff {N : Submodule R M} : IsIsotypicOfType R N 
S ↔ forall m <= N, [IsSimpleModule R m] -> Nonempty (m ≃ₗ[R] S)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.forall'`：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Pr
op}, (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用定理 `Submodule.map_subtype_le`：map_subtype_le (p' : Submodule R p) : map p.su
btype p' <= p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearEquiv.isSimpleModule_iff`：LinearEquiv.isSimpleModule_iff (e : M ≃ₗ
[R] N) : IsSimpleModule R M ↔ IsSimpleModule R N
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
-/
theorem isIsotypicOfType_submodule_iff {N : Submodule R M} :
    IsIsotypicOfType R N S ↔ ∀ m ≤ N, [IsSimpleModule R m] → Nonempty (m ≃ₗ[R] S) := by
  rw [Subtype.forall', ← (Submodule.MapSubtype.orderIso N).forall_congr_right]
  have e := Submodule.equivMapOfInjective _ N.subtype_injective
  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff]
  exact forall₂_congr fun m _ ↦ ⟨fun ⟨e'⟩ ↦ ⟨(e m).symm.trans e'⟩, fun ⟨e'⟩ ↦ ⟨(e m).trans e'⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**isIsotypic_submodule_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIsotypic_submodule_iff {N : Submodule R M} : IsIsotypic R N ↔ forall m <
= N, [IsSimpleModule R m] -> IsIsotypicOfType R N m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.forall'`：∀ {α : Sort u_1} {p : α → Prop} {q : (x : α) → p x → Pr
op}, (∀ (x : α) (h : p x), q x h) ↔ ∀ (x : { a // p a }), q ↑x ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用定理 `Submodule.map_subtype_le`：map_subtype_le (p' : Submodule R p) : map p.su
btype p' <= p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearEquiv.isSimpleModule_iff`：LinearEquiv.isSimpleModule_iff (e : M ≃ₗ
[R] N) : IsSimpleModule R M ↔ IsSimpleModule R N
· 使用定理 `LinearEquiv.isIsotypicOfType_iff_type`：LinearEquiv.isIsotypicOfType_iff_
type (e : N ≃ₗ[R] S) : IsIsotypicOfType R M N ↔ IsIsotypicOfType R M S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isIsotypic_submodule_iff {N : Submodule R M} :
    IsIsotypic R N ↔ ∀ m ≤ N, [IsSimpleModule R m] → IsIsotypicOfType R N m := by
  rw [Subtype.forall', ← (Submodule.MapSubtype.orderIso N).forall_congr_right]
  have e := Submodule.equivMapOfInjective _ N.subtype_injective
  simp_rw [Submodule.MapSubtype.orderIso, Equiv.coe_fn_mk, ← (e _).isSimpleModule_iff,
    ← (e _).isIsotypicOfType_iff_type, IsIsotypic]

section Finsupp

variable [IsSemisimpleModule R M]

/-
**IsIsotypicOfType.linearEquiv_finsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypicOfType.linearEquiv_finsupp (h : IsIsotypicOfType R M S) : exists
 ι : Type u, Nonempty (M ≃ₗ[R] ι ->₀ S)
参数：h : IsIsotypicOfType R M S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemisimpleModule.exists_linearEquiv_dfinsupp`：IsSemisimpleModule.exist
s_linearEquiv_dfinsupp [IsSemisimpleModule R M] : exists (s : Set (Submodule R M
)) (_ : M ≃ₗ[R] Π₀ m : s, m.1), sSup…
-/
theorem IsIsotypicOfType.linearEquiv_finsupp (h : IsIsotypicOfType R M S) :
    ∃ ι : Type u, Nonempty (M ≃ₗ[R] ι →₀ S) := by
  have ⟨s, e, _, hs⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R M
  classical exact ⟨s, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun m : s ↦ (h m.1).some)
    |>.trans (finsuppLequivDFinsupp R).symm⟩⟩
/-
**IsIsotypic.linearEquiv_finsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypic.linearEquiv_finsupp [Nontrivial M] (h : IsIsotypic R M) : exist
s (ι : Type u) (_ : Nonempty ι) (S : Submodule R M), IsSimpleModule R S ∧ Nonemp
ty (M ≃ₗ[R] ι ->₀ S)
参数：h : IsIsotypic R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAtomic.exists_atom`：IsAtomic.exists_atom [OrderBot α] [Nontrivial α] [
IsAtomic α] : exists a : α, IsAtom a
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `isAtomic_of_complementedLattice`：∀ {α : Type u_2} [inst : CompleteLattic
e α] [IsModularLattice α] [IsCompactlyGenerated α] [ComplementedLattice α],   Is
Atomic α
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `Submodule.instIsCompactlyGenerated`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   IsCom
pactlyGenerated (Submodu…
· 使用定理 `IsSemisimpleModule.toComplementedLattice`：∀ {R : Type u_2} {inst : Ring 
R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self
 : IsSemisimpleModule R M], Co…
· 使用定理 `IsIsotypicOfType.linearEquiv_finsupp`：IsIsotypicOfType.linearEquiv_finsu
pp (h : IsIsotypicOfType R M S) : exists ι : Type u, Nonempty (M ≃ₗ[R] ι ->₀ S)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isSimpleModule_iff_isAtom`：isSimpleModule_iff_isAtom : IsSimpleModule R 
m ↔ IsAtom m
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
-/
theorem IsIsotypic.linearEquiv_finsupp [Nontrivial M] (h : IsIsotypic R M) :
    ∃ (ι : Type u) (_ : Nonempty ι) (S : Submodule R M),
      IsSimpleModule R S ∧ Nonempty (M ≃ₗ[R] ι →₀ S) := by
  have ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  rw [← isSimpleModule_iff_isAtom] at hS
  have ⟨ι, e⟩ := (h S).linearEquiv_finsupp
  exact ⟨ι, (isEmpty_or_nonempty ι).resolve_left fun _ ↦ not_subsingleton _ (e.some.subsingleton),
    S, hS, e⟩
/-
**IsIsotypicOfType.linearEquiv_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypicOfType.linearEquiv_fun [Module.Finite R M] (h : IsIsotypicOfType
 R M S) : exists n : Nat, Nonempty (M ≃ₗ[R] Fin n -> S)
参数：h : IsIsotypicOfType R M S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp`：IsSemisimpleModule.e
xists_linearEquiv_fin_dfinsupp [IsSemisimpleModule R M] [Module.Finite R M] : ex
ists (n : Nat) (S : Fin n -> Submodule R…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem IsIsotypicOfType.linearEquiv_fun [Module.Finite R M] (h : IsIsotypicOfType R M S) :
    ∃ n : ℕ, Nonempty (M ≃ₗ[R] Fin n → S) := by
  have ⟨n, S, e, hs⟩ := IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp R M
  classical exact ⟨n, ⟨e.trans (DFinsupp.mapRange.linearEquiv fun i ↦ (h (S i)).some)
    |>.trans (finsuppLequivDFinsupp R).symm |>.trans (Finsupp.linearEquivFunOnFinite ..)⟩⟩
/-
**IsIsotypic.linearEquiv_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypic.linearEquiv_fun [Module.Finite R M] [Nontrivial M] (h : IsIsoty
pic R M) : exists (n : Nat) (_ : NeZero n) (S : Submodule R M), IsSimpleModule R
 S ∧ Nonempty (M ≃ₗ[R] Fin n -> S)
参数：h : IsIsotypic R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAtomic.exists_atom`：IsAtomic.exists_atom [OrderBot α] [Nontrivial α] [
IsAtomic α] : exists a : α, IsAtom a
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `isAtomic_of_complementedLattice`：∀ {α : Type u_2} [inst : CompleteLattic
e α] [IsModularLattice α] [IsCompactlyGenerated α] [ComplementedLattice α],   Is
Atomic α
· 使用定理 `Submodule.instIsModularLattice`：∀ {R : Type u_10} {M : Type u_11} [inst 
: Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsModularLat
tice (Submodule R M)
· 使用定理 `Submodule.instIsCompactlyGenerated`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   IsCom
pactlyGenerated (Submodu…
· 使用定理 `IsSemisimpleModule.toComplementedLattice`：∀ {R : Type u_2} {inst : Ring 
R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self
 : IsSemisimpleModule R M], Co…
· 使用定理 `IsIsotypicOfType.linearEquiv_fun`：IsIsotypicOfType.linearEquiv_fun [Modu
le.Finite R M] (h : IsIsotypicOfType R M S) : exists n : Nat, Nonempty (M ≃ₗ[R] 
Fin n -> S)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isSimpleModule_iff_isAtom`：isSimpleModule_iff_isAtom : IsSimpleModule R 
m ↔ IsAtom m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neZero_iff`：∀ {R : Type u_1} [inst : Zero R] {n : R}, NeZero n ↔ n ≠ 0
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem IsIsotypic.linearEquiv_fun [Module.Finite R M] [Nontrivial M] (h : IsIsotypic R M) :
    ∃ (n : ℕ) (_ : NeZero n) (S : Submodule R M),
      IsSimpleModule R S ∧ Nonempty (M ≃ₗ[R] Fin n → S) := by
  have ⟨S, hS⟩ := IsAtomic.exists_atom (Submodule R M)
  rw [← isSimpleModule_iff_isAtom] at hS
  have ⟨n, e⟩ := (h S).linearEquiv_fun
  exact ⟨n, neZero_iff.2 <| by rintro rfl; exact not_subsingleton _ (e.some.subsingleton), S, hS, e⟩
/-
**IsIsotypic.submodule_linearEquiv_fun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypic.submodule_linearEquiv_fun {m : Submodule R M} [Module.Finite R 
m] [Nontrivial m] (h : IsIsotypic R m) : exists (n : Nat) (_ : NeZero n) (S : Su
bmodule R M), S <= m ∧ IsSimpleModule R S ∧ Nonempty (m ≃ₗ[R] Fin n -> S)
参数：h : IsIsotypic R m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypic.linearEquiv_fun`：IsIsotypic.linearEquiv_fun [Module.Finite R 
M] [Nontrivial M] (h : IsIsotypic R M) : exists (n : Nat) (_ : NeZero n) (S : Su
bmodule R M), Is…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用定理 `Submodule.map_subtype_le`：map_subtype_le (p' : Submodule R p) : map p.su
btype p' <= p
· 使用定理 `IsSimpleModule.congr`：IsSimpleModule.congr (e : M ≃ₗ[R] N) [IsSimpleModu
le R N] : IsSimpleModule R M where __
-/
theorem IsIsotypic.submodule_linearEquiv_fun {m : Submodule R M} [Module.Finite R m] [Nontrivial m]
    (h : IsIsotypic R m) : ∃ (n : ℕ) (_ : NeZero n) (S : Submodule R M),
      S ≤ m ∧ IsSimpleModule R S ∧ Nonempty (m ≃ₗ[R] Fin n → S) :=
  have ⟨n, hn, S, _, ⟨e⟩⟩ := h.linearEquiv_fun
  let e' := S.equivMapOfInjective _ m.subtype_injective
  ⟨n, hn, _, m.map_subtype_le S, .congr e'.symm, ⟨e.trans <| .piCongrRight fun _ ↦ e'⟩⟩

end Finsupp

variable (R M S)

/-- If `S` is a simple `R`-module, the `S`-isotypic component in an `R`-module `M` is the sum of
all submodules of `M` isomorphic to `S`. -/
/-
**isotypicComponent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isotypicComponent : Submodule R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is a simple `R`-module, the `S`-isotypic component in an `R`-module `M` i
s the sum of
all submodules of `M` isomorphic to `S`.
-/
def isotypicComponent : Submodule R M := sSup {m | Nonempty (m ≃ₗ[R] S)}

/-- The set of all (nontrivial) isotypic components of a module. -/
/-
**isotypicComponents** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：isotypicComponents : Set (Submodule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of all (nontrivial) isotypic components of a module.
-/
def isotypicComponents : Set (Submodule R M) :=
  { m | ∃ S : Submodule R M, IsSimpleModule R S ∧ m = isotypicComponent R M S }

variable {R M}
/-
**Submodule.le_isotypicComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.le_isotypicComponent (m : Submodule R M) : m <= isotypicComponen
t R M m
参数：m : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
-/
theorem Submodule.le_isotypicComponent (m : Submodule R M) : m ≤ isotypicComponent R M m :=
  le_sSup ⟨.refl ..⟩
/-
**bot_lt_isotypicComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_lt_isotypicComponent (S : Submodule R M) [IsSimpleModule R S] : ⊥ < is
otypicComponent R M S
参数：S : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot : Nontrivial p ↔ 
p != ⊥
· 使用定理 `IsSimpleModule.nontrivial`：IsSimpleModule.nontrivial [IsSimpleModule R M
] : Nontrivial M
· 使用定理 `Submodule.le_isotypicComponent`：Submodule.le_isotypicComponent (m : Subm
odule R M) : m <= isotypicComponent R M m
-/
theorem bot_lt_isotypicComponent (S : Submodule R M) [IsSimpleModule R S] :
    ⊥ < isotypicComponent R M S :=
  (bot_lt_iff_ne_bot.mpr <| (S.nontrivial_iff_ne_bot).mp <| IsSimpleModule.nontrivial R S).trans_le
    S.le_isotypicComponent
/-
**bot_lt_isotypicComponents** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：bot_lt_isotypicComponents {m : Submodule R M} (h : m in isotypicComponents
 R M) : ⊥ < m
参数：h : m in isotypicComponents R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_lt_isotypicComponent`：bot_lt_isotypicComponent (S : Submodule R M) [
IsSimpleModule R S] : ⊥ < isotypicComponent R M S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bot_lt_isotypicComponents {m : Submodule R M} (h : m ∈ isotypicComponents R M) : ⊥ < m := by
  obtain ⟨_, _, rfl⟩ := h; exact bot_lt_isotypicComponent ..
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : isotypicComponents R M) : Nontrivial c :=
  Submodule.nontrivial_iff_ne_bot.mpr (bot_lt_isotypicComponents c.2).ne'
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsSemisimpleModule R S] : IsSemisimpleModule R (isotypicComponent R M S) := by
  rw [isotypicComponent, sSup_eq_iSup]
  refine isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m ⟨e⟩ ↦ ?_
  have := IsSemisimpleModule.congr e
  infer_instance
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : isotypicComponents R M) : IsSemisimpleModule R c := by
  obtain ⟨c, S, _, rfl⟩ := c; infer_instance

variable {S} in
/-
**LinearEquiv.isotypicComponent_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isotypicComponent_eq (e : N ≃ₗ[R] S) : isotypicComponent R M N
 = isotypicComponent R M S
参数：e : N ≃ₗ[R] S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Nonempty.congr`：∀ {α : Sort u_3} {β : Sort u_4} (f : α → β) (g : β → α),
 Nonempty α ↔ Nonempty β
-/
theorem LinearEquiv.isotypicComponent_eq (e : N ≃ₗ[R] S) :
    isotypicComponent R M N = isotypicComponent R M S :=
  congr_arg sSup <| Set.ext fun _ ↦ Nonempty.congr (·.trans e) (·.trans e.symm)

section SimpleSubmodule

variable (N : Submodule R M) [IsSimpleModule R N] (s : Set (Submodule R M))

open LinearMap in
/-
**Submodule.le_linearEquiv_of_sSup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.le_linearEquiv_of_sSup_eq_top [IsSemisimpleModule R M] (hs : sSu
p s = ⊤) : exists m in s, exists S <= m, Nonempty (N ≃ₗ[R] S)
参数：hs : sSup s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSimpleModule.nontrivial`：IsSimpleModule.nontrivial [IsSimpleModule R M
] : Nontrivial M
· 使用定理 `ComplementedLattice.exists_isCompl`：∀ {α : Type u_2} {inst : Lattice α} 
{inst_1 : BoundedOrder α} [self : ComplementedLattice α] (a : α), ∃ b, IsCompl a
 b
· 使用定理 `IsSemisimpleModule.toComplementedLattice`：∀ {R : Type u_2} {inst : Ring 
R} {M : Type u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self
 : IsSemisimpleModule R M], Co…
· 使用定理 `LinearMap.exists_ne_zero_of_sSup_eq_top`：exists_ne_zero_of_sSup_eq_top {
f : M ->ₛₗ[τ₁₂] M₂} (h : f != 0) (s : Set (Submodule R M)) (hs : sSup s = ⊤) : e
xists m in s, f ∘ₛₗ m.subtype…
· 使用定理 `LinearMap.ne_zero_of_surjective`：ne_zero_of_surjective [Nontrivial M₂] {
f : M ->ₛₗ[σ₁₂] M₂} (hf : Surjective f) : f != 0
· 使用定理 `Submodule.projectionOnto_surjective`：projectionOnto_surjective (h : IsCo
mpl p q) : Function.Surjective (projectionOnto p q h)
· 使用定理 `LinearMap.linearEquiv_of_ne_zero`：linearEquiv_of_ne_zero [IsSemisimpleMo
dule R M] [IsSimpleModule R N] {f : M ->ₗ[R] N} (h : f != 0) : exists S : Submod
ule R M, Nonempty (N ≃…
· 使用定理 `Submodule.map_subtype_le`：map_subtype_le (p' : Submodule R p) : map p.su
btype p' <= p
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
-/
theorem Submodule.le_linearEquiv_of_sSup_eq_top [IsSemisimpleModule R M]
    (hs : sSup s = ⊤) : ∃ m ∈ s, ∃ S ≤ m, Nonempty (N ≃ₗ[R] S) := by
  have := IsSimpleModule.nontrivial R N
  have ⟨_, compl⟩ := exists_isCompl N
  have ⟨m, hm, ne⟩ := exists_ne_zero_of_sSup_eq_top (ne_zero_of_surjective
    (projectionOnto_surjective compl)) _ hs
  have ⟨S, ⟨e⟩⟩ := linearEquiv_of_ne_zero ne
  exact ⟨m, hm, _, m.map_subtype_le S, ⟨e.trans (S.equivMapOfInjective _ m.subtype_injective)⟩⟩
/-
**Submodule.linearEquiv_of_sSup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.linearEquiv_of_sSup_eq_top [h : forall m : s, IsSimpleModule R m
] (hs : sSup s = ⊤) : exists S in s, Nonempty (N ≃ₗ[R] S)
参数：hs : sSup s = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `isSemisimpleModule_of_isSemisimpleModule_submodule'`：isSemisimpleModule_
of_isSemisimpleModule_submodule' {p : ι -> Submodule R M} (hp : forall i, IsSemi
simpleModule R (p i)) (hp' : ⨆ i, p i = ⊤…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `Submodule.le_linearEquiv_of_sSup_eq_top`：Submodule.le_linearEquiv_of_sSu
p_eq_top [IsSemisimpleModule R M] (hs : sSup s = ⊤) : exists m in s, exists S <=
 m, Nonempty (N ≃ₗ[R] S)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSimpleModule_iff_isAtom`：isSimpleModule_iff_isAtom : IsSimpleModule R 
m ↔ IsAtom m
· 使用定理 `IsSimpleModule.congr`：IsSimpleModule.congr (e : M ≃ₗ[R] N) [IsSimpleModu
le R N] : IsSimpleModule R M where __
· 使用引理 `IsAtom.le_iff_eq`：IsAtom.le_iff_eq (ha : IsAtom a) (hb : b != ⊥) : b <= 
a ↔ b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Submodule.linearEquiv_of_sSup_eq_top [h : ∀ m : s, IsSimpleModule R m]
    (hs : sSup s = ⊤) : ∃ S ∈ s, Nonempty (N ≃ₗ[R] S) :=
  have := isSemisimpleModule_of_isSemisimpleModule_submodule' (fun _ ↦ inferInstance)
    (sSup_eq_iSup' s ▸ hs)
  have ⟨m, hm, _S, le, ⟨e⟩⟩ := N.le_linearEquiv_of_sSup_eq_top _ hs
  have := isSimpleModule_iff_isAtom.mp (IsSimpleModule.congr e.symm)
  have := ((isSimpleModule_iff_isAtom.mp <| h ⟨m, hm⟩).le_iff_eq this.1).mp le
  ⟨m, hm, ⟨e.trans (.ofEq _ _ this)⟩⟩

/-- If a simple module is contained in a sum of semisimple modules, it must be isomorphic
to a submodule of one of the summands. -/
/-
**Submodule.le_linearEquiv_of_le_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.le_linearEquiv_of_le_sSup [hs : forall m : s, IsSemisimpleModule
 R m] (hN : N <= sSup s) : exists m in s, exists S <= m, Nonempty (N ≃ₗ[R] S)
参数：hN : N <= sSup s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
· 使用定理 `IsSimpleModule.congr`：IsSimpleModule.congr (e : M ≃ₗ[R] N) [IsSimpleModu
le R N] : IsSimpleModule R M where __
· 使用引理 `isSemisimpleModule_biSup_of_isSemisimpleModule_submodule`：isSemisimpleMo
dule_biSup_of_isSemisimpleModule_submodule {s : Set ι} {p : ι -> Submodule R M} 
(hp : forall i in s, IsSemisimpleModule R (p i…
· 使用定理 `Submodule.le_linearEquiv_of_sSup_eq_top`：Submodule.le_linearEquiv_of_sSu
p_eq_top [IsSemisimpleModule R M] (hs : sSup s = ⊤) : exists m in s, exists S <=
 m, Nonempty (N ≃ₗ[R] S)
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用引理 `Submodule.biSup_comap_subtype_eq_top`：biSup_comap_subtype_eq_top {ι : Ty
pe*} (s : Set ι) (p : ι -> Submodule R M) : ⨆ i in s, (p i).comap (⨆ i in s, p i
).subtype = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype

--- 原说明 ---
If a simple module is contained in a sum of semisimple modules, it must be isomo
rphic
to a submodule of one of the summands.
-/
theorem Submodule.le_linearEquiv_of_le_sSup [hs : ∀ m : s, IsSemisimpleModule R m]
    (hN : N ≤ sSup s) : ∃ m ∈ s, ∃ S ≤ m, Nonempty (N ≃ₗ[R] S) := by
  rw [sSup_eq_iSup] at hN
  have e := LinearEquiv.ofInjective _ (inclusion_injective hN)
  have := IsSimpleModule.congr e.symm
  have := isSemisimpleModule_biSup_of_isSemisimpleModule_submodule fun m hm ↦ hs ⟨m, hm⟩
  obtain ⟨_, ⟨m, hm, rfl⟩, S, le, ⟨e'⟩⟩ := LinearMap.range (inclusion hN)
      |>.le_linearEquiv_of_sSup_eq_top (comap (⨆ i ∈ s, i).subtype '' s) <| by
    rw [sSup_image, biSup_comap_subtype_eq_top]
  exact ⟨m, hm, _, map_le_iff_le_comap.mpr le,
    ⟨(e.trans e').trans (equivMapOfInjective _ (subtype_injective _) _)⟩⟩
/-
**Submodule.linearEquiv_of_le_sSup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.linearEquiv_of_le_sSup [simple : forall m : s, IsSimpleModule R 
m] (hs : N <= sSup s) : exists S in s, Nonempty (N ≃ₗ[R] S)
参数：hs : N <= sSup s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.le_linearEquiv_of_le_sSup`：Submodule.le_linearEquiv_of_le_sSup
 [hs : forall m : s, IsSemisimpleModule R m] (hN : N <= sSup s) : exists m in s,
 exists S <= m, Nonempty …
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSimpleModule_iff_isAtom`：isSimpleModule_iff_isAtom : IsSimpleModule R 
m ↔ IsAtom m
· 使用定理 `IsSimpleModule.congr`：IsSimpleModule.congr (e : M ≃ₗ[R] N) [IsSimpleModu
le R N] : IsSimpleModule R M where __
· 使用引理 `IsAtom.le_iff_eq`：IsAtom.le_iff_eq (ha : IsAtom a) (hb : b != ⊥) : b <= 
a ↔ b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Submodule.linearEquiv_of_le_sSup [simple : ∀ m : s, IsSimpleModule R m]
    (hs : N ≤ sSup s) : ∃ S ∈ s, Nonempty (N ≃ₗ[R] S) :=
  have ⟨m, hm, _S, le, ⟨e⟩⟩ := N.le_linearEquiv_of_le_sSup _ hs
  have := isSimpleModule_iff_isAtom.mp (.congr e.symm)
  have := ((isSimpleModule_iff_isAtom.mp <| simple ⟨m, hm⟩).le_iff_eq this.1).mp le
  ⟨m, hm, ⟨e.trans (.ofEq _ _ this)⟩⟩

end SimpleSubmodule

section IsSimpleModule

variable (R M) [IsSimpleModule R S]

local instance (m : {m : Submodule R M | Nonempty (m ≃ₗ[R] S)}) : IsSimpleModule R m :=
  .congr m.2.some

/-
**IsIsotypicOfType.isotypicComponent** 是 Mathlib 中的一个定理，位于命名空间 `IsIsotypicOfType
`。
形式化陈述：∀ (R : Type u_2) (M : Type u) (S : Type u_4) [inst : Ring R] [inst_1 : Add
CommGroup M] [inst_2 : AddCommGroup S]   [inst_3 : _root_.Module R M] [inst_4 : 
_root_.Module R S] [IsSimpleModule R S],   IsIsotypicOfType R (↥(isotypicCompone
nt R M S)) S
参数：R : Type u_2；M : Type u；S : Type u_4；↥(isotypicComponent R M S)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isIsotypicOfType_submodule_iff`：isIsotypicOfType_submodule_iff {N : Subm
odule R M} : IsIsotypicOfType R N S ↔ forall m <= N, [IsSimpleModule R m] -> Non
empty (m ≃ₗ[R] S)
· 使用定理 `Submodule.linearEquiv_of_le_sSup`：Submodule.linearEquiv_of_le_sSup [simp
le : forall m : s, IsSimpleModule R m] (hs : N <= sSup s) : exists S in s, Nonem
pty (N ≃ₗ[R] S)
· 使用定理 `instIsSimpleModuleSubtypeMemSubmoduleValSetOfPredNonemptyLinearEquivId`：
∀ (R : Type u_2) (M : Type u) (S : Type u_4) [inst : Ring R] [inst_1 : AddCommGr
oup M] [inst_2 : AddCommGroup S]   [inst_3 : _root_.Module R…
-/
protected theorem IsIsotypicOfType.isotypicComponent :
    IsIsotypicOfType R (isotypicComponent R M S) S :=
  isIsotypicOfType_submodule_iff.mpr fun m h _ ↦
    have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_le_sSup _ h
    ⟨e'.trans e⟩
/-
**IsIsotypic.isotypicComponent** 是 Mathlib 中的一个定理，位于命名空间 `IsIsotypic`。
形式化陈述：∀ (R : Type u_2) (M : Type u) (S : Type u_4) [inst : Ring R] [inst_1 : Add
CommGroup M] [inst_2 : AddCommGroup S]   [inst_3 : _root_.Module R M] [inst_4 : 
_root_.Module R S] [IsSimpleModule R S],   IsIsotypic R ↥(isotypicComponent R M 
S)
参数：R : Type u_2；M : Type u；S : Type u_4；isotypicComponent R M S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypicOfType.isIsotypic`：IsIsotypicOfType.isIsotypic (h : IsIsotypic
OfType R M S) : IsIsotypic R M
· 使用定理 `IsIsotypicOfType.isotypicComponent`：∀ (R : Type u_2) (M : Type u) (S : T
ype u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup S]   [
inst_3 : _root_.Module R…
-/
protected theorem IsIsotypic.isotypicComponent : IsIsotypic R (isotypicComponent R M S) :=
  (IsIsotypicOfType.isotypicComponent R M S).isIsotypic

variable {R M} in
/-
**IsIsotypic.isotypicComponents** 是 Mathlib 中的一个定理，位于命名空间 `IsIsotypic`。
形式化陈述：∀ {R : Type u_2} {M : Type u} [inst : Ring R] [inst_1 : AddCommGroup M] [i
nst_2 : _root_.Module R M]   {m : Submodule R M}, m ∈ isotypicComponents R M → I
sIsotypic R ↥m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypic.isotypicComponent`：∀ (R : Type u_2) (M : Type u) (S : Type u_
4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup S]   [inst_3
 : _root_.Module R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem IsIsotypic.isotypicComponents {m : Submodule R M}
    (h : m ∈ isotypicComponents R M) : IsIsotypic R m := by
  obtain ⟨_, _, rfl⟩ := h; exact .isotypicComponent R M _

variable {R M} in
/-
**eq_isotypicComponent_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_isotypicComponent_of_le {S c : Submodule R M} (hc : c in isotypicCompon
ents R M) [IsSimpleModule R S] (le : S <= c) : c = isotypicComponent R M S
参数：hc : c in isotypicComponents R M；le : S <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIsotypicOfType_submodule_iff`：isIsotypicOfType_submodule_iff {N : Subm
odule R M} : IsIsotypicOfType R N S ↔ forall m <= N, [IsSimpleModule R m] -> Non
empty (m ≃ₗ[R] S)
· 使用定理 `IsIsotypicOfType.isotypicComponent`：∀ (R : Type u_2) (M : Type u) (S : T
ype u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup S]   [
inst_3 : _root_.Module R…
· 使用定理 `LinearEquiv.isotypicComponent_eq`：LinearEquiv.isotypicComponent_eq (e : 
N ≃ₗ[R] S) : isotypicComponent R M N = isotypicComponent R M S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_isotypicComponent_of_le {S c : Submodule R M} (hc : c ∈ isotypicComponents R M)
    [IsSimpleModule R S] (le : S ≤ c) : c = isotypicComponent R M S := by
  obtain ⟨S', _, rfl⟩ := hc
  have ⟨e⟩ := isIsotypicOfType_submodule_iff.mp (.isotypicComponent R M S') _ le
  exact e.symm.isotypicComponent_eq
/-
**sSupIndep_isotypicComponents** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSupIndep_isotypicComponents : sSupIndep (isotypicComponents R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `of_not_not`：of_not_not {a : Prop} : ¬¬a -> a
· 使用定理 `instIsSemisimpleModuleSubtypeMemSubmoduleIsotypicComponent`：∀ {R : Type 
u_2} {M : Type u} (S : Type u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst
_2 : AddCommGroup S]   [inst_3 : _root_.Module R…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSemisimpleModule.of_injective`：of_injective (f : N ->ₗ[R] M) (hf : Fun
ction.Injective f) : IsSemisimpleModule R N
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsSemisimpleModule.eq_bot_or_exists_simple_le`：eq_bot_or_exists_simple_l
e (N : Submodule R M) [IsSemisimpleModule R N] : N = ⊥ ∨ exists m <= N, IsSimple
Module R m
· 使用定理 `Submodule.le_linearEquiv_of_le_sSup`：Submodule.le_linearEquiv_of_le_sSup
 [hs : forall m : s, IsSemisimpleModule R m] (hN : N <= sSup s) : exists m in s,
 exists S <= m, Nonempty …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `IsSimpleModule.congr`：IsSimpleModule.congr (e : M ≃ₗ[R] N) [IsSimpleModu
le R N] : IsSimpleModule R M where __
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_isotypicComponent_of_le`：eq_isotypicComponent_of_le {S c : Submodule 
R M} (hc : c in isotypicComponents R M) [IsSimpleModule R S] (le : S <= c) : c =
 isotypicCompone…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearEquiv.isotypicComponent_eq`：LinearEquiv.isotypicComponent_eq (e : 
N ≃ₗ[R] S) : isotypicComponent R M N = isotypicComponent R M S
-/
theorem sSupIndep_isotypicComponents : sSupIndep (isotypicComponents R M) :=
  fun c hc ↦ disjoint_iff.mpr <| of_not_not fun ne ↦ by
    set s := isotypicComponents R M \ {c}
    have : IsSemisimpleModule R c := by obtain ⟨S, _, rfl⟩ := hc; infer_instance
    have := IsSemisimpleModule.of_injective _
      (Submodule.inclusion_injective (inf_le_left : c ⊓ sSup s ≤ c))
    have (c : s) : IsSemisimpleModule R c := by obtain ⟨_, ⟨_, _, rfl⟩, _⟩ := c; infer_instance
    have ⟨S, le, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le _).resolve_left ne
    have ⟨c', hc', S', le', ⟨e⟩⟩ := S.le_linearEquiv_of_le_sSup _ (le.trans inf_le_right)
    have := IsSimpleModule.congr e.symm
    refine hc'.2 ?_
    rw [eq_isotypicComponent_of_le hc (le.trans inf_le_left), eq_isotypicComponent_of_le hc'.1 le']
    exact e.symm.isotypicComponent_eq
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsNoetherian R M] : Finite (isotypicComponents R M) :=
  Set.finite_coe_iff.mpr <| WellFoundedGT.finite_of_sSupIndep (sSupIndep_isotypicComponents R M)

variable {R M S}
/-
**IsIsotypicOfType.of_isotypicComponent_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIsotypicOfType.of_isotypicComponent_eq_top (h : isotypicComponent R M S 
= ⊤) : IsIsotypicOfType R M S
参数：h : isotypicComponent R M S = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.linearEquiv_of_sSup_eq_top`：Submodule.linearEquiv_of_sSup_eq_t
op [h : forall m : s, IsSimpleModule R m] (hs : sSup s = ⊤) : exists S in s, Non
empty (N ≃ₗ[R] S)
· 使用定理 `instIsSimpleModuleSubtypeMemSubmoduleValSetOfPredNonemptyLinearEquivId`：
∀ (R : Type u_2) (M : Type u) (S : Type u_4) [inst : Ring R] [inst_1 : AddCommGr
oup M] [inst_2 : AddCommGroup S]   [inst_3 : _root_.Module R…
-/
theorem IsIsotypicOfType.of_isotypicComponent_eq_top (h : isotypicComponent R M S = ⊤) :
    IsIsotypicOfType R M S :=
  fun m _ ↦ have ⟨_, ⟨e⟩, ⟨e'⟩⟩ := m.linearEquiv_of_sSup_eq_top _ h; ⟨e'.trans e⟩
/-
**Submodule.map_le_isotypicComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.map_le_isotypicComponent (S : Submodule R M) [IsSimpleModule R S
] (f : M ->ₗ[R] N) : S.map f <= isotypicComponent R N S
参数：S : Submodule R M；f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `LinearMap.injective_or_eq_zero`：injective_or_eq_zero [IsSimpleModule R M
] (f : M ->ₗ[R] N) : Function.Injective f ∨ f = 0
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.range.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u
_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `LinearMap.range_zero`：range_zero [RingHomSurjective τ₁₂] : range (0 : M 
->ₛₗ[τ₁₂] M₂) = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem Submodule.map_le_isotypicComponent (S : Submodule R M) [IsSimpleModule R S]
    (f : M →ₗ[R] N) : S.map f ≤ isotypicComponent R N S := by
  conv_lhs => rw [← S.range_subtype, ← LinearMap.range_comp]
  obtain inj | eq := (f ∘ₗ S.subtype).injective_or_eq_zero
  · exact le_sSup ⟨.symm <| .ofInjective _ inj⟩
  · simp_rw [eq, LinearMap.range_zero, bot_le]

variable (S) in
/-
**LinearMap.le_comap_isotypicComponent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.le_comap_isotypicComponent (f : M ->ₗ[R] N) : isotypicComponent 
R M S <= (isotypicComponent R N S).comap f
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `IsSimpleModule.congr`：IsSimpleModule.congr (e : M ≃ₗ[R] N) [IsSimpleModu
le R N] : IsSimpleModule R M where __
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Submodule.map_le_isotypicComponent`：Submodule.map_le_isotypicComponent (
S : Submodule R M) [IsSimpleModule R S] (f : M ->ₗ[R] N) : S.map f <= isotypicCo
mponent R N S
· 使用定理 `LinearEquiv.isotypicComponent_eq`：LinearEquiv.isotypicComponent_eq (e : 
N ≃ₗ[R] S) : isotypicComponent R M N = isotypicComponent R M S
-/
theorem LinearMap.le_comap_isotypicComponent (f : M →ₗ[R] N) :
    isotypicComponent R M S ≤ (isotypicComponent R N S).comap f :=
  sSup_le fun m ⟨e⟩ ↦ Submodule.map_le_iff_le_comap.mp <|
    have := IsSimpleModule.congr e
    (m.map_le_isotypicComponent f).trans_eq e.isotypicComponent_eq

section IsFullyInvariant

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- A submodule `N` an `R`-module `M` is fully invariant if `N` is mapped into itself by all
`R`-linear endomorphisms of `M`.

If `M` is semisimple, this is equivalent to `N` being a sum of isotypic components of `M`:
see `isFullyInvariant_iff_sSup_isotypicComponents`. -/
/-
**Submodule.IsFullyInvariant** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.IsFullyInvariant (N : Submodule R M) : Prop
参数：N : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule `N` an `R`-module `M` is fully invariant if `N` is mapped into itsel
f by all
`R`-linear endomorphisms of `M`.

If `M` is semisimple, this is equivalent to `N` being a sum of isotypic componen
ts of `M`:
see `isFullyInvariant_iff_sSup_isotypicComponents`.
-/
def Submodule.IsFullyInvariant (N : Submodule R M) : Prop :=
  ∀ f : Module.End R M, N ≤ N.comap f
/-
**isFullyInvariant_iff_isTwoSided** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isFullyInvariant_iff_isTwoSided {I : Ideal R} : I.IsFullyInvariant ↔ I.IsT
woSided
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∀ (a : α), q (e a)) ↔ ∀ (b : β), q b
· 使用定理 `Ideal.isTwoSided_iff`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 
I.IsTwoSided ↔ ∀ {a : α} (b : α), a ∈ I → a * b ∈ I
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem isFullyInvariant_iff_isTwoSided {I : Ideal R} : I.IsFullyInvariant ↔ I.IsTwoSided := by
  simpa only [Submodule.IsFullyInvariant, ← MulOpposite.opEquiv.trans (RingEquiv.moduleEndSelf R
    |>.toEquiv) |>.forall_congr_right, SetLike.le_def, I.isTwoSided_iff] using! forall_comm

variable (R M) in
/-- The fully invariant submodules of a module form a complete sublattice in the lattice of
submodules. -/
/-
**fullyInvariantSubmodule** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fullyInvariantSubmodule : CompleteSublattice (Submodule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fully invariant submodules of a module form a complete sublattice in the lat
tice of
submodules.
-/
def fullyInvariantSubmodule : CompleteSublattice (Submodule R M) :=
  .mk' { N : Submodule R M | N.IsFullyInvariant }
    (fun _s hs f ↦ sSup_le fun _N hN ↦ (hs hN f).trans <| Submodule.comap_mono <| le_sSup hN)
    fun _s hs f ↦ Submodule.map_le_iff_le_comap.mp <| le_sInf fun _N hN ↦
      Submodule.map_le_iff_le_comap.mpr <| (sInf_le hN).trans (hs hN f)
/-
**mem_fullyInvariantSubmodule_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_fullyInvariantSubmodule_iff {m : Submodule R M} : m in fullyInvariantS
ubmodule R M ↔ m.IsFullyInvariant
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_fullyInvariantSubmodule_iff {m : Submodule R M} :
    m ∈ fullyInvariantSubmodule R M ↔ m.IsFullyInvariant := Iff.rfl

end IsFullyInvariant

section Equiv

variable {ι : Type*} [DecidableEq ι] {N : ι → Submodule R M}
  (ind : iSupIndep N) (iSup_top : ⨆ i, N i = ⊤) (invar : ∀ i, (N i).IsFullyInvariant)

set_option backward.isDefEq.respectTransparency.types false in
/-- If an `R`-module `M` is the direct sum of fully invariant submodules `Nᵢ`,
then `End R M` is isomorphic to `Πᵢ End R Nᵢ` as a ring. -/
/-
**iSupIndep.ringEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSupIndep.ringEquiv : Module.End R M ≃+* Π i, Module.End R (N i) where toF
un f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an `R`-module `M` is the direct sum of fully invariant submodules `Nᵢ`,
then `End R M` is isomorphic to `Πᵢ End R Nᵢ` as a ring.
-/
noncomputable def iSupIndep.ringEquiv : Module.End R M ≃+* Π i, Module.End R (N i) where
  toFun f i := f.restrict (invar i f)
  invFun f := letI e := ind.linearEquiv iSup_top; e ∘ₗ DFinsupp.mapRange.linearMap f ∘ₗ e.symm
  left_inv f := LinearMap.ext fun x ↦ by
    exact Submodule.iSup_induction _ (motive := (_ = f ·)) (iSup_top ▸ Submodule.mem_top (x := x))
      (fun i x h ↦ by simp [ind.linearEquiv_symm_apply _ h]) (by simp)
      fun _ _ h₁ h₂ ↦ by simpa only [map_add] using congr($h₁ + $h₂)
  right_inv f := by ext i x; simp [ind.linearEquiv_symm_apply _ x.2]
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- If an `R`-module `M` is the direct sum of fully invariant submodules `Nᵢ`,
then `End R M` is isomorphic to `Πᵢ End R Nᵢ` as an algebra. -/
/-
**iSupIndep.algEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSupIndep.algEquiv [Module R₀ M] [IsScalarTower R₀ R M] : Module.End R M ≃
ₐ[R₀] Π i, Module.End R (N i) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If an `R`-module `M` is the direct sum of fully invariant submodules `Nᵢ`,
then `End R M` is isomorphic to `Πᵢ End R Nᵢ` as an algebra.
-/
noncomputable def iSupIndep.algEquiv [Module R₀ M] [IsScalarTower R₀ R M] :
    Module.End R M ≃ₐ[R₀] Π i, Module.End R (N i) where
  __ := ind.ringEquiv iSup_top invar
  commutes' _ := rfl

end Equiv

variable (R M S) in
/-
**Submodule.IsFullyInvariant.isotypicComponent** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule.IsFullyInvariant`。
形式化陈述：∀ (R : Type u_2) (M : Type u) (S : Type u_4) [inst : Ring R] [inst_1 : Add
CommGroup M] [inst_2 : AddCommGroup S]   [inst_3 : _root_.Module R M] [inst_4 : 
_root_.Module R S] [IsSimpleModule R S],   (isotypicComponent R M S).IsFullyInva
riant
参数：R : Type u_2；M : Type u；S : Type u_4；isotypicComponent R M S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.le_comap_isotypicComponent`：LinearMap.le_comap_isotypicCompone
nt (f : M ->ₗ[R] N) : isotypicComponent R M S <= (isotypicComponent R N S).comap
 f
-/
protected theorem Submodule.IsFullyInvariant.isotypicComponent :
    (isotypicComponent R M S).IsFullyInvariant :=
  LinearMap.le_comap_isotypicComponent S
/-
**Submodule.IsFullyInvariant.of_mem_isotypicComponents** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Submodule.IsFullyInvariant.of_mem_isotypicComponents {m : Submodule R M} (
h : m in isotypicComponents R M) : m.IsFullyInvariant
参数：h : m in isotypicComponents R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsFullyInvariant.isotypicComponent`：∀ (R : Type u_2) (M : Type
 u) (S : Type u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGr
oup S]   [inst_3 : _root_.Module R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Submodule.IsFullyInvariant.of_mem_isotypicComponents {m : Submodule R M}
    (h : m ∈ isotypicComponents R M) : m.IsFullyInvariant := by
  obtain ⟨_, _, rfl⟩ := h; exact .isotypicComponent R M _

variable (R M) in
/-- The Galois coinsertion from sets of isotypic components to fully invariant submodules. -/
/-
**GaloisCoinsertion.setIsotypicComponents** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GaloisCoinsertion.setIsotypicComponents : GaloisCoinsertion (α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Galois coinsertion from sets of isotypic components to fully invariant submo
dules.
-/
def GaloisCoinsertion.setIsotypicComponents :
    GaloisCoinsertion (α := Set (isotypicComponents R M)) (β := fullyInvariantSubmodule R M)
      (fun s ↦ ⨆ c ∈ s, ⟨c, .of_mem_isotypicComponents c.2⟩) fun m ↦ {c | c.1 ≤ m} :=
  GaloisConnection.toGaloisCoinsertion (fun _ _ ↦ iSup₂_le_iff) fun s c hc ↦ of_not_not fun hcs ↦
    (bot_lt_isotypicComponents c.2).ne' <| (sSupIndep_isotypicComponents R M c.2).eq_bot_of_le <|
    hc.trans <| by
      simp_rw [CompleteSublattice.coe_iSup, iSup₂_le_iff]
      exact fun c hc ↦ le_sSup ⟨c.2, Subtype.coe_ne_coe.mpr (ne_of_mem_of_not_mem hc hcs)⟩
/-
**le_isotypicComponent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_isotypicComponent_iff [IsSemisimpleModule R M] {m : Submodule R M} : m 
<= isotypicComponent R M S ↔ IsIsotypicOfType R m S where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypicOfType.of_injective`：IsIsotypicOfType.of_injective (h : IsIsot
ypicOfType R N S) (f : M ->ₗ[R] N) (inj : Function.Injective f) : IsIsotypicOfTy
pe R M S
· 使用定理 `IsIsotypicOfType.isotypicComponent`：∀ (R : Type u_2) (M : Type u) (S : T
ype u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup S]   [
inst_3 : _root_.Module R…
· 使用定理 `Submodule.inclusion_injective`：inclusion_injective (h : p <= p') : Funct
ion.Injective (inclusion h)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsSemisimpleModule.sSup_simples_le`：sSup_simples_le (N : Submodule R M) 
: sSup { m : Submodule R M | IsSimpleModule R m ∧ m <= N } = N
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIsotypicOfType_submodule_iff`：isIsotypicOfType_submodule_iff {N : Subm
odule R M} : IsIsotypicOfType R N S ↔ forall m <= N, [IsSimpleModule R m] -> Non
empty (m ≃ₗ[R] S)
-/
theorem le_isotypicComponent_iff [IsSemisimpleModule R M] {m : Submodule R M} :
    m ≤ isotypicComponent R M S ↔ IsIsotypicOfType R m S where
  mp h := .of_injective (.isotypicComponent R M S) _ (Submodule.inclusion_injective h)
  mpr h := (IsSemisimpleModule.sSup_simples_le m).ge.trans
    (sSup_le_sSup fun S ⟨_, le⟩ ↦ isIsotypicOfType_submodule_iff.mp h S le)
/-
**isotypicComponent_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isotypicComponent_eq_top_iff [IsSemisimpleModule R M] : isotypicComponent 
R M S = ⊤ ↔ IsIsotypicOfType R M S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `le_isotypicComponent_iff`：le_isotypicComponent_iff [IsSemisimpleModule R
 M] {m : Submodule R M} : m <= isotypicComponent R M S ↔ IsIsotypicOfType R m S 
where mp h
· 使用定理 `LinearEquiv.isIsotypicOfType_iff`：LinearEquiv.isIsotypicOfType_iff (e : 
M ≃ₗ[R] N) : IsIsotypicOfType R M S ↔ IsIsotypicOfType R N S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isotypicComponent_eq_top_iff [IsSemisimpleModule R M] :
    isotypicComponent R M S = ⊤ ↔ IsIsotypicOfType R M S := by
  rw [← top_le_iff, le_isotypicComponent_iff, Submodule.topEquiv.isIsotypicOfType_iff]

open IsSemisimpleModule in
/-
**isFullyInvariant_iff_le_imp_isotypicComponent_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isFullyInvariant_iff_le_imp_isotypicComponent_le [IsSemisimpleModule R M] 
{m : Submodule R M} : m.IsFullyInvariant ↔ forall S <= m, [IsSimpleModule R S] -
> isotypicComponent R M S <= m where mp h S le _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `IsSemisimpleModule.extension_property`：extension_property {P} [AddCommGr
oup P] [Module R P] (f : N ->ₗ[R] M) (hf : Function.Injective f) (g : N ->ₗ[R] P
) : exists h : M ->ₗ[R] P, …
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `LinearEquiv.range_comp`：range_comp [RingHomSurjective σ₂₃] [RingHomSurje
ctive σ₁₃] : LinearMap.range (h.comp (e : M ->ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = Li
nearMap.rang…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsSemisimpleModule.sSup_simples_le`：sSup_simples_le (N : Submodule R M) 
: sSup { m : Submodule R M | IsSimpleModule R m ∧ m <= N } = N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.map_le_isotypicComponent`：Submodule.map_le_isotypicComponent (
S : Submodule R M) [IsSimpleModule R S] (f : M ->ₗ[R] N) : S.map f <= isotypicCo
mponent R N S
-/
theorem isFullyInvariant_iff_le_imp_isotypicComponent_le [IsSemisimpleModule R M]
    {m : Submodule R M} :
    m.IsFullyInvariant ↔ ∀ S ≤ m, [IsSimpleModule R S] → isotypicComponent R M S ≤ m where
  mp h S le _ := sSup_le fun S' ⟨e⟩ ↦ by
    have ⟨p, eq⟩ := extension_property _ S.subtype_injective (S'.subtype ∘ₗ e.symm)
    refine le_trans ?_ (Submodule.map_le_iff_le_comap.mpr (le.trans (h p)))
    rw [← S.range_subtype, ← LinearMap.range_comp, eq, e.symm.range_comp, S'.range_subtype]
  mpr h f := (sSup_simples_le m).ge.trans <| sSup_le fun S ⟨_, le⟩ ↦
    Submodule.map_le_iff_le_comap.mp ((S.map_le_isotypicComponent f).trans (h S le))
/-
**eq_isotypicComponent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_isotypicComponent_iff [IsSemisimpleModule R M] {m : Submodule R M} (ne 
: m != ⊥) : m = isotypicComponent R M S ↔ IsIsotypicOfType R m S ∧ m.IsFullyInva
riant where mp
参数：ne : m != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypicOfType.isotypicComponent`：∀ (R : Type u_2) (M : Type u) (S : T
ype u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup S]   [
inst_3 : _root_.Module R…
· 使用定理 `Submodule.IsFullyInvariant.isotypicComponent`：∀ (R : Type u_2) (M : Type
 u) (S : Type u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGr
oup S]   [inst_3 : _root_.Module R…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_isotypicComponent_iff`：le_isotypicComponent_iff [IsSemisimpleModule R
 M] {m : Submodule R M} : m <= isotypicComponent R M S ↔ IsIsotypicOfType R m S 
where mp h
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsSemisimpleModule.eq_bot_or_exists_simple_le`：eq_bot_or_exists_simple_l
e (N : Submodule R M) [IsSemisimpleModule R N] : N = ⊥ ∨ exists m <= N, IsSimple
Module R m
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `LinearEquiv.isotypicComponent_eq`：LinearEquiv.isotypicComponent_eq (e : 
N ≃ₗ[R] S) : isotypicComponent R M N = isotypicComponent R M S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIsotypicOfType_submodule_iff`：isIsotypicOfType_submodule_iff {N : Subm
odule R M} : IsIsotypicOfType R N S ↔ forall m <= N, [IsSimpleModule R m] -> Non
empty (m ≃ₗ[R] S)
· 使用定理 `isFullyInvariant_iff_le_imp_isotypicComponent_le`：isFullyInvariant_iff_l
e_imp_isotypicComponent_le [IsSemisimpleModule R M] {m : Submodule R M} : m.IsFu
llyInvariant ↔ forall S <= m, [IsSimpl…
-/
theorem eq_isotypicComponent_iff [IsSemisimpleModule R M] {m : Submodule R M} (ne : m ≠ ⊥) :
    m = isotypicComponent R M S ↔ IsIsotypicOfType R m S ∧ m.IsFullyInvariant where
  mp := by rintro rfl; exact ⟨.isotypicComponent R M S, .isotypicComponent R M S⟩
  mpr := fun ⟨iso, invar⟩ ↦ (le_isotypicComponent_iff.mpr iso).antisymm <|
    have ⟨S', le, _⟩ := (IsSemisimpleModule.eq_bot_or_exists_simple_le m).resolve_left ne
    (isIsotypicOfType_submodule_iff.mp iso S' le).some.symm.isotypicComponent_eq.trans_le
      (isFullyInvariant_iff_le_imp_isotypicComponent_le.mp invar _ le)

end IsSimpleModule

variable [IsSemisimpleModule R M]

open IsSemisimpleModule

/-
**isIsotypic_iff_isFullyInvariant_imp_bot_or_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isIsotypic_iff_isFullyInvariant_imp_bot_or_top : IsIsotypic R M ↔ forall N
 : Submodule R M, N.IsFullyInvariant -> N = ⊥ ∨ N = ⊤ where mp h N hN
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isotypicComponent_eq_top_iff`：isotypicComponent_eq_top_iff [IsSemisimple
Module R M] : isotypicComponent R M S = ⊤ ↔ IsIsotypicOfType R M S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isFullyInvariant_iff_le_imp_isotypicComponent_le`：isFullyInvariant_iff_l
e_imp_isotypicComponent_le [IsSemisimpleModule R M] {m : Submodule R M} : m.IsFu
llyInvariant ↔ forall S <= m, [IsSimpl…
· 使用定理 `IsSemisimpleModule.eq_bot_or_exists_simple_le`：eq_bot_or_exists_simple_l
e (N : Submodule R M) [IsSemisimpleModule R N] : N = ⊥ ∨ exists m <= N, IsSimple
Module R m
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Submodule.IsFullyInvariant.isotypicComponent`：∀ (R : Type u_2) (M : Type
 u) (S : Type u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGr
oup S]   [inst_3 : _root_.Module R…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `bot_lt_isotypicComponent`：bot_lt_isotypicComponent (S : Submodule R M) [
IsSimpleModule R S] : ⊥ < isotypicComponent R M S
-/
theorem isIsotypic_iff_isFullyInvariant_imp_bot_or_top :
    IsIsotypic R M ↔ ∀ N : Submodule R M, N.IsFullyInvariant → N = ⊥ ∨ N = ⊤ where
  mp h N hN := (eq_bot_or_exists_simple_le N).imp_right fun ⟨S, le, _⟩ ↦ top_unique <|
    (isotypicComponent_eq_top_iff.mpr (h S)).ge.trans
    ((isFullyInvariant_iff_le_imp_isotypicComponent_le.mp hN) _ le)
  mpr h S _ := isotypicComponent_eq_top_iff.mp <|
    (h _ (.isotypicComponent R M S)).resolve_left (bot_lt_isotypicComponent S).ne'
/-
**mem_isotypicComponents_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_isotypicComponents_iff {m : Submodule R M} : m in isotypicComponents R
 M ↔ IsIsotypic R m ∧ m.IsFullyInvariant ∧ m != ⊥ where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIsotypic.isotypicComponent`：∀ (R : Type u_2) (M : Type u) (S : Type u_
4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup S]   [inst_3
 : _root_.Module R…
· 使用定理 `Submodule.IsFullyInvariant.isotypicComponent`：∀ (R : Type u_2) (M : Type
 u) (S : Type u_4) [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGr
oup S]   [inst_3 : _root_.Module R…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `bot_lt_isotypicComponent`：bot_lt_isotypicComponent (S : Submodule R M) [
IsSimpleModule R S] : ⊥ < isotypicComponent R M S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsSemisimpleModule.eq_bot_or_exists_simple_le`：eq_bot_or_exists_simple_l
e (N : Submodule R M) [IsSemisimpleModule R N] : N = ⊥ ∨ exists m <= N, IsSimple
Module R m
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_isotypicComponent_iff`：eq_isotypicComponent_iff [IsSemisimpleModule R
 M] {m : Submodule R M} (ne : m != ⊥) : m = isotypicComponent R M S ↔ IsIsotypic
OfType R m S ∧…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIsotypic_submodule_iff`：isIsotypic_submodule_iff {N : Submodule R M} :
 IsIsotypic R N ↔ forall m <= N, [IsSimpleModule R m] -> IsIsotypicOfType R N m
-/
theorem mem_isotypicComponents_iff {m : Submodule R M} :
    m ∈ isotypicComponents R M ↔ IsIsotypic R m ∧ m.IsFullyInvariant ∧ m ≠ ⊥ where
  mp := by rintro ⟨S, _, rfl⟩; exact ⟨.isotypicComponent R M S,
    .isotypicComponent R M S, (bot_lt_isotypicComponent S).ne'⟩
  mpr := fun ⟨iso, invar, ne⟩ ↦
    have ⟨S, le, simple⟩ := (eq_bot_or_exists_simple_le m).resolve_left ne
    ⟨S, simple, (eq_isotypicComponent_iff ne).mpr ⟨isIsotypic_submodule_iff.mp iso S le, invar⟩⟩

/-- Sets of isotypic components in a semisimple module are in order-preserving 1-1
correspondence with fully invariant submodules. Consequently, the fully invariant submodules
form a complete atomic Boolean algebra. -/
/-
**OrderIso.setIsotypicComponents** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：{R : Type u_2} →   {M : Type u} →     [inst : Ring R] →       [inst_1 : Ad
dCommGroup M] →         [inst_2 : _root_.Module R M] →           [IsSemisimpleMo
dule R M] → Set ↑(isotypicComponents R M) ≃o ↥(fullyInvariantSubmodule R M)
参数：isotypicComponents R M；fullyInvariantSubmodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sets of isotypic components in a semisimple module are in order-preserving 1-1
correspondence with fully invariant submodules. Consequently, the fully invarian
t submodules
form a complete atomic Boolean algebra.
-/
@[simps] def OrderIso.setIsotypicComponents :
    Set (isotypicComponents R M) ≃o fullyInvariantSubmodule R M where
  toFun s := ⨆ c ∈ s, ⟨c, .of_mem_isotypicComponents c.2⟩
  invFun m := { c | c.1 ≤ m }
  left_inv := (GaloisCoinsertion.setIsotypicComponents R M).u_l_eq
  right_inv m := (iSup₂_le fun _ ↦ by exact id).antisymm <| (sSup_simples_le m.1).ge.trans <|
      sSup_le fun S ⟨simple, le⟩ ↦ S.le_isotypicComponent.trans <| by
    let c : isotypicComponents R M := ⟨_, S, simple, rfl⟩
    simp_rw [← show c.1 = isotypicComponent R M S from rfl, CompleteSublattice.coe_iSup]
    exact le_biSup _ (isFullyInvariant_iff_le_imp_isotypicComponent_le.mp m.2 _ le)
  map_rel_iff' := (GaloisCoinsertion.setIsotypicComponents R M).l_le_l_iff

set_option backward.isDefEq.respectTransparency.types false in
/-
**isFullyInvariant_iff_sSup_isotypicComponents** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isFullyInvariant_iff_sSup_isotypicComponents {m : Submodule R M} : m.IsFul
lyInvariant ↔ exists s subseteq isotypicComponents R M, m = sSup s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_image`：sSup_image {s : Set β} {f : β -> α} : sSup (f '' s) = ⨆ a in
 s, f a
· 使用定理 `CompleteSublattice.coe_iSup`：∀ {α : Type u_1} [inst : CompleteLattice α]
 {L : CompleteSublattice α} {ι : Sort u_3} (f : ι → ↥L),   ↑(iSup f) = ⨆ i, ↑(f 
i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `CompleteSublattice.sSupClosed`：sSupClosed {s : Set α} (h : s subseteq L)
 : sSup s in L
· 使用定理 `Submodule.IsFullyInvariant.of_mem_isotypicComponents`：Submodule.IsFullyI
nvariant.of_mem_isotypicComponents {m : Submodule R M} (h : m in isotypicCompone
nts R M) : m.IsFullyInvariant
-/
theorem isFullyInvariant_iff_sSup_isotypicComponents {m : Submodule R M} :
    m.IsFullyInvariant ↔ ∃ s ⊆ isotypicComponents R M, m = sSup s := by
  refine ⟨fun h ↦ ⟨OrderIso.setIsotypicComponents.symm ⟨m, h⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · rintro _ ⟨c, _, rfl⟩; exact c.2
  · convert! Subtype.ext_iff.mp (OrderIso.setIsotypicComponents.right_inv ⟨m, h⟩).symm
    simp [sSup_image, OrderIso.setIsotypicComponents, OrderIso.symm]
  · rintro ⟨_, hs, rfl⟩
    exact (fullyInvariantSubmodule R M).sSupClosed fun _ h ↦ .of_mem_isotypicComponents (hs h)

variable (R M) in
/-
**sSup_isotypicComponents** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_isotypicComponents : sSup (isotypicComponents R M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isFullyInvariant_iff_sSup_isotypicComponents`：isFullyInvariant_iff_sSup_
isotypicComponents {m : Submodule R M} : m.IsFullyInvariant ↔ exists s subseteq 
isotypicComponents R M, m = sSup s
· 使用定理 `CompleteSublattice.top_mem`：top_mem : ⊤ in L
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
-/
theorem sSup_isotypicComponents : sSup (isotypicComponents R M) = ⊤ :=
  have ⟨_, h, eq⟩ := isFullyInvariant_iff_sSup_isotypicComponents.mp
    (fullyInvariantSubmodule R M).top_mem
  top_unique <| eq.le.trans (sSup_le_sSup h)

namespace IsSemisimpleModule

variable (R M) [Module R₀ M] [IsScalarTower R₀ R M] [DecidableEq (isotypicComponents R M)]

/-- The endomorphism algebra of a semisimple module is the direct product of the endomorphism
algebras of its isotypic components. -/
/-
**IsSemisimpleModule.endAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsSemisimpleModule`。
形式化陈述：endAlgEquiv : Module.End R M ≃ₐ[R₀] Π c : isotypicComponents R M, Module.E
nd R c.1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The endomorphism algebra of a semisimple module is the direct product of the end
omorphism
algebras of its isotypic components.
-/
noncomputable def endAlgEquiv :
    Module.End R M ≃ₐ[R₀] Π c : isotypicComponents R M, Module.End R c.1 :=
  ((sSupIndep_iff _).mp <| sSupIndep_isotypicComponents R M).algEquiv R₀
    ((sSup_eq_iSup' _).symm.trans <| sSup_isotypicComponents R M) (.of_mem_isotypicComponents ·.2)

/-- The endomorphism ring of a semisimple module is the direct product of the endomorphism rings
of its isotypic components. -/
/-
**IsSemisimpleModule.endRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `IsSemisimpleModule`
。
形式化陈述：endRingEquiv : Module.End R M ≃+* Π c : isotypicComponents R M, Module.End
 R c.1
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The endomorphism ring of a semisimple module is the direct product of the endomo
rphism rings
of its isotypic components.
-/
noncomputable def endRingEquiv :
    Module.End R M ≃+* Π c : isotypicComponents R M, Module.End R c.1 :=
  (endAlgEquiv ℕ R M).toRingEquiv

end IsSemisimpleModule

