/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Lie.Semisimple.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# Lie algebras with non-degenerate invariant bilinear forms are semisimple

In this file we prove that a finite-dimensional Lie algebra over a field is semisimple
if it does not have non-trivial abelian ideals and it admits a
non-degenerate reflexive invariant bilinear form.
Here a form is *invariant* if it is invariant under the Lie bracket
in the sense that `⁅x, Φ⁆ = 0` for all `x` or equivalently, `Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆`.

## Main results

* `LieAlgebra.InvariantForm.orthogonal`: given a Lie submodule `N` of a Lie module `M`,
  we define its orthogonal complement with respect to a non-degenerate invariant bilinear form `Φ`
  as the Lie ideal of elements `x` such that `Φ n x = 0` for all `n ∈ N`.
* `LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate`: the main result of this file;
  a finite-dimensional Lie algebra over a field is semisimple
  if it does not have non-trivial abelian ideals and admits
  a non-degenerate invariant reflexive bilinear form.

## References

We follow the short and excellent paper [dieudonne1953].
-/

@[expose] public section

namespace LieAlgebra

namespace InvariantForm

section ring

variable {R L M : Type*}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]

variable (Φ : LinearMap.BilinForm R M) (hΦ_nondeg : Φ.Nondegenerate)

variable (L) in
/--
A bilinear form on a Lie module `M` of a Lie algebra `L` is *invariant* if
for all `x : L` and `y z : M` the condition `Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆` holds.
-/
/-
**LieAlgebra.InvariantForm._root_.LinearMap.BilinForm.lieInvariant** 是 Mathlib 中
的一个定义，位于命名空间 `LieAlgebra.InvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bilinear form on a Lie module `M` of a Lie algebra `L` is *invariant* if
for all `x : L` and `y z : M` the condition `Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆` holds.
-/
def _root_.LinearMap.BilinForm.lieInvariant : Prop :=
  ∀ (x : L) (y z : M), Φ ⁅x, y⁆ z = -Φ y ⁅x, z⁆
/-
**LieAlgebra.InvariantForm._root_.LinearMap.BilinForm.lieInvariant_iff** 是 Mathl
ib 中的一个引理，位于命名空间 `LieAlgebra.InvariantForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearMap.BilinForm.lieInvariant_iff [LieAlgebra R L] [LieModule R L M] :
    Φ.lieInvariant L ↔ Φ ∈ LieModule.maxTrivSubmodule R L (LinearMap.BilinForm R M) := by
  refine ⟨fun h x ↦ ?_, fun h x y z ↦ ?_⟩
  · ext y z
    rw [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply, LinearMap.zero_apply,
      LinearMap.zero_apply, h, sub_self]
  · replace h := LinearMap.congr_fun₂ (h x) y z
    simp only [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply,
      LinearMap.zero_apply, sub_eq_zero] at h
    simp [← h]

/--
The orthogonal complement of a Lie submodule `N` with respect to an invariant bilinear form `Φ` is
the Lie submodule of elements `y` such that `Φ x y = 0` for all `x ∈ N`.
-/
@[simps!]
/-
**LieAlgebra.InvariantForm.orthogonal** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Inva
riantForm`。
形式化陈述：orthogonal (hΦ_inv : Φ.lieInvariant L) (N : LieSubmodule R L M) : LieSubmo
dule R L M where __
参数：hΦ_inv : Φ.lieInvariant L；N : LieSubmodule R L M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal complement of a Lie submodule `N` with respect to an invariant bi
linear form `Φ` is
the Lie submodule of elements `y` such that `Φ x y = 0` for all `x ∈ N`.
-/
def orthogonal (hΦ_inv : Φ.lieInvariant L) (N : LieSubmodule R L M) : LieSubmodule R L M where
  __ := Φ.orthogonal N
  lie_mem {x y} := by
    suffices (∀ n ∈ N, Φ n y = 0) → ∀ n ∈ N, Φ n ⁅x, y⁆ = 0 by
      simpa only [
        AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup, Submodule.mem_toAddSubmonoid,
        LinearMap.BilinForm.mem_orthogonal_iff, LieSubmodule.mem_toSubmodule]
    intro H a ha
    rw [← neg_eq_zero, ← hΦ_inv]
    exact H _ <| N.lie_mem ha

variable (hΦ_inv : Φ.lieInvariant L)

@[simp]
/-
**LieAlgebra.InvariantForm.orthogonal_toSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `Lie
Algebra.InvariantForm`。
形式化陈述：orthogonal_toSubmodule (N : LieSubmodule R L M) : (orthogonal Φ hΦ_inv N).
toSubmodule = Φ.orthogonal N.toSubmodule
参数：N : LieSubmodule R L M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma orthogonal_toSubmodule (N : LieSubmodule R L M) :
    (orthogonal Φ hΦ_inv N).toSubmodule = Φ.orthogonal N.toSubmodule := rfl
/-
**LieAlgebra.InvariantForm.mem_orthogonal** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.
InvariantForm`。
形式化陈述：mem_orthogonal (N : LieSubmodule R L M) (y : M) : y in orthogonal Φ hΦ_inv
 N ↔ forall x in N, Φ x y = 0
参数：N : LieSubmodule R L M；y : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_orthogonal (N : LieSubmodule R L M) (y : M) :
    y ∈ orthogonal Φ hΦ_inv N ↔ ∀ x ∈ N, Φ x y = 0 := by
  simp [orthogonal, LinearMap.BilinForm.mem_orthogonal_iff]

variable [LieAlgebra R L]
/-
**LieAlgebra.InvariantForm.orthogonal_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `LieAlg
ebra.InvariantForm`。
形式化陈述：orthogonal_disjoint (Φ : LinearMap.BilinForm R L) (hΦ_nondeg : Φ.Nondegene
rate) (hΦ_inv : Φ.lieInvariant L) -- TODO: replace the following assumption by a
 typeclass assumption `[HasNonAbelianAtoms]` (hL : forall I : LieIdeal R L, IsAt
om I -> ¬IsLieAbelian I) (I : LieIdeal R L) (hI : IsAtom I) : Disjoint I (orthog
onal Φ hΦ_inv I)
参数：Φ : LinearMap.BilinForm R L；hΦ_nondeg : Φ.Nondegenerate；hΦ_inv : Φ.lieInvaria
nt L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsAtom.lt_iff`：IsAtom.lt_iff (h : IsAtom a) : x < a ↔ x = ⊥
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `lie_eq_self_of_isAtom_of_nonabelian`：lie_eq_self_of_isAtom_of_nonabelian
 {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (I : LieIdeal R L) (hI 
: IsAtom I) (h : ¬IsLieAb…
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `lie_mem_left`：lie_mem_left (I : LieIdeal R L) (x y : L) (h : x in I) : ⁅
x, y⁆ in I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma orthogonal_disjoint
    (Φ : LinearMap.BilinForm R L) (hΦ_nondeg : Φ.Nondegenerate) (hΦ_inv : Φ.lieInvariant L)
    -- TODO: replace the following assumption by a typeclass assumption `[HasNonAbelianAtoms]`
    (hL : ∀ I : LieIdeal R L, IsAtom I → ¬IsLieAbelian I)
    (I : LieIdeal R L) (hI : IsAtom I) :
    Disjoint I (orthogonal Φ hΦ_inv I) := by
  rw [disjoint_iff, ← hI.lt_iff, lt_iff_le_and_ne]
  suffices ¬I ≤ orthogonal Φ hΦ_inv I by simpa
  intro contra
  apply hI.1
  rw [eq_bot_iff, ← lie_eq_self_of_isAtom_of_nonabelian I hI (hL I hI),
      LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [LieSubmodule.bot_coe, Set.mem_singleton_iff]
  apply hΦ_nondeg.1
  intro z
  rw [hΦ_inv, neg_eq_zero]
  have hyz : ⁅(x : L), z⁆ ∈ I := lie_mem_left _ _ _ _ _ x.2
  exact contra hyz y y.2

end ring

section field

variable {K L M : Type*}
variable [Field K] [LieRing L] [LieAlgebra K L]
variable [AddCommGroup M] [Module K M] [LieRingModule L M]

variable [Module.Finite K L]
variable (Φ : LinearMap.BilinForm K L) (hΦ_nondeg : Φ.Nondegenerate)
variable (hΦ_inv : Φ.lieInvariant L) (hΦ_refl : Φ.IsRefl)
-- TODO: replace the following assumption by a typeclass assumption `[HasNonAbelianAtoms]`
variable (hL : ∀ I : LieIdeal K L, IsAtom I → ¬IsLieAbelian I)
include hΦ_nondeg hΦ_refl hL

open Module Submodule in
/-
**LieAlgebra.InvariantForm.orthogonal_isCompl_toSubmodule** 是 Mathlib 中的一个引理，位于命
名空间 `LieAlgebra.InvariantForm`。
形式化陈述：orthogonal_isCompl_toSubmodule (I : LieIdeal K L) (hI : IsAtom I) : IsComp
l I.toSubmodule (orthogonal Φ hΦ_inv I).toSubmodule
参数：I : LieIdeal K L；hI : IsAtom I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieAlgebra.InvariantForm.orthogonal_toSubmodule`：orthogonal_toSubmodule 
(N : LieSubmodule R L M) : (orthogonal Φ hΦ_inv N).toSubmodule = Φ.orthogonal N.
toSubmodule
· 使用引理 `LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint`：isCompl_orthogonal_
iff_disjoint (hB₀ : B.IsRefl) : IsCompl W (B.orthogonal W) ↔ Disjoint W (B.ortho
gonal W)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.disjoint_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `LieAlgebra.InvariantForm.orthogonal_disjoint`：orthogonal_disjoint (Φ : L
inearMap.BilinForm R L) (hΦ_nondeg : Φ.Nondegenerate) (hΦ_inv : Φ.lieInvariant L
) -- TODO: replace the following a…
-/
lemma orthogonal_isCompl_toSubmodule (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I.toSubmodule (orthogonal Φ hΦ_inv I).toSubmodule := by
  rw [orthogonal_toSubmodule, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hΦ_refl,
      ← orthogonal_toSubmodule _ hΦ_inv, LieSubmodule.disjoint_toSubmodule]
  exact orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI

open Module Submodule in
/-
**LieAlgebra.InvariantForm.orthogonal_isCompl** 是 Mathlib 中的一个引理，位于命名空间 `LieAlge
bra.InvariantForm`。
形式化陈述：orthogonal_isCompl (I : LieIdeal K L) (hI : IsAtom I) : IsCompl I (orthogo
nal Φ hΦ_inv I)
参数：I : LieIdeal K L；hI : IsAtom I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.isCompl_toSubmodule`：∀ {R : Type u} {L : Type v} {M : Type 
w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 
: _root_.Module R M] […
· 使用引理 `LieAlgebra.InvariantForm.orthogonal_isCompl_toSubmodule`：orthogonal_isCo
mpl_toSubmodule (I : LieIdeal K L) (hI : IsAtom I) : IsCompl I.toSubmodule (orth
ogonal Φ hΦ_inv I).toSubmodule
-/
lemma orthogonal_isCompl (I : LieIdeal K L) (hI : IsAtom I) :
    IsCompl I (orthogonal Φ hΦ_inv I) := by
  rw [← LieSubmodule.isCompl_toSubmodule]
  exact orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI

include hΦ_inv
/-
**LieAlgebra.InvariantForm.restrict_nondegenerate** 是 Mathlib 中的一个引理，位于命名空间 `Lie
Algebra.InvariantForm`。
形式化陈述：restrict_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) : (Φ.restrict I)
.Nondegenerate
参数：I : LieIdeal K L；hI : IsAtom I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal`：restr
ict_nondegenerate_iff_isCompl_orthogonal (b₁ : B.IsRefl) : (B.restrict W).Nondeg
enerate ↔ IsCompl W (B.orthogonal W)
· 使用引理 `LieAlgebra.InvariantForm.orthogonal_isCompl_toSubmodule`：orthogonal_isCo
mpl_toSubmodule (I : LieIdeal K L) (hI : IsAtom I) : IsCompl I.toSubmodule (orth
ogonal Φ hΦ_inv I).toSubmodule
-/
lemma restrict_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict I).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  exact orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI
/-
**LieAlgebra.InvariantForm.restrict_orthogonal_nondegenerate** 是 Mathlib 中的一个引理，
位于命名空间 `LieAlgebra.InvariantForm`。
形式化陈述：restrict_orthogonal_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) : (Φ.
restrict (orthogonal Φ hΦ_inv I)).Nondegenerate
参数：I : LieIdeal K L；hI : IsAtom I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal`：restr
ict_nondegenerate_iff_isCompl_orthogonal (b₁ : B.IsRefl) : (B.restrict W).Nondeg
enerate ↔ IsCompl W (B.orthogonal W)
· 使用引理 `LinearMap.BilinForm.orthogonal_orthogonal`：orthogonal_orthogonal (hB : B
.Nondegenerate) (hB₀ : B.IsRefl) (W : Submodule K V) : B.orthogonal (B.orthogona
l W) = W
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用引理 `LieAlgebra.InvariantForm.orthogonal_isCompl_toSubmodule`：orthogonal_isCo
mpl_toSubmodule (I : LieIdeal K L) (hI : IsAtom I) : IsCompl I.toSubmodule (orth
ogonal Φ hΦ_inv I).toSubmodule
-/
lemma restrict_orthogonal_nondegenerate (I : LieIdeal K L) (hI : IsAtom I) :
    (Φ.restrict (orthogonal Φ hΦ_inv I)).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hΦ_refl]
  simp only [LieIdeal.toLieSubalgebra_toSubmodule, orthogonal_toSubmodule,
    LinearMap.BilinForm.orthogonal_orthogonal hΦ_nondeg hΦ_refl]
  exact (orthogonal_isCompl_toSubmodule Φ hΦ_nondeg hΦ_inv hΦ_refl hL I hI).symm

open Module Submodule in
/-
**LieAlgebra.InvariantForm.atomistic** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.Invar
iantForm`。
形式化陈述：atomistic : forall I : LieIdeal K L, sSup {J : LieIdeal K L | IsAtom J ∧ J
 <= I} = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsAtomic.eq_bot_or_exists_atom_le`：∀ {α : Type u_2} {inst : PartialOrder
 α} {inst_1 : OrderBot α} [self : IsAtomic α] (b : α),   b = ⊥ ∨ ∃ a, IsAtom a ∧
 a ≤ b
· 使用定理 `LieSubmodule.instIsAtomicOfIsArtinian`：∀ (R : Type u) (L : Type v) (M : 
Type w) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [in
st_3 : _root_.Module R M] […
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
· 使用引理 `LieAlgebra.InvariantForm.orthogonal_isCompl`：orthogonal_isCompl (I : Lie
Ideal K L) (hI : IsAtom I) : IsCompl I (orthogonal Φ hΦ_inv I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_inf_assoc_of_le`：sup_inf_assoc_of_le {x : α} (y : α) {z : α} (h : x 
<= z) : (x ⊔ y) ⊓ z = x ⊔ y ⊓ z
· 使用定理 `LieSubmodule.instIsModularLattice`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `Submodule.finrank_lt_finrank_of_lt`：finrank_lt_finrank_of_lt {s t : Subm
odule K V} [FiniteDimensional K t] (hst : s < t) : finrank K s < finrank K t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `LieAlgebra.InvariantForm.orthogonal_disjoint`：orthogonal_disjoint (Φ : L
inearMap.BilinForm R L) (hΦ_nondeg : Φ.Nondegenerate) (hΦ_inv : Φ.lieInvariant L
) -- TODO: replace the following a…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 33 条，此处仅展示前 30 条）
-/
lemma atomistic : ∀ I : LieIdeal K L, sSup {J : LieIdeal K L | IsAtom J ∧ J ≤ I} = I := by
  intro I
  apply le_antisymm
  · apply sSup_le
    rintro J ⟨-, hJ'⟩
    exact hJ'
  by_cases hI : I = ⊥
  · exact hI.le.trans bot_le
  obtain ⟨J, hJ, hJI⟩ := (eq_bot_or_exists_atom_le I).resolve_left hI
  let J' := orthogonal Φ hΦ_inv J
  suffices I ≤ J ⊔ (J' ⊓ I) by
    refine this.trans ?_
    apply sup_le
    · exact le_sSup ⟨hJ, hJI⟩
    rw [← atomistic (J' ⊓ I)]
    apply sSup_le_sSup
    simp only [le_inf_iff, Set.ofPred_subset_ofPred, and_imp]
    tauto
  suffices J ⊔ J' = ⊤ by rw [← sup_inf_assoc_of_le _ hJI, this, top_inf_eq]
  exact (orthogonal_isCompl Φ hΦ_nondeg hΦ_inv hΦ_refl hL J hJ).codisjoint.eq_top
termination_by I => finrank K I
decreasing_by
  apply finrank_lt_finrank_of_lt
  suffices ¬I ≤ J' by simpa
  intro hIJ'
  apply hJ.1
  rw [eq_bot_iff]
  exact orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL J hJ le_rfl (hJI.trans hIJ')

open LieSubmodule in
/--
A finite-dimensional Lie algebra over a field is semisimple
if it does not have non-trivial abelian ideals and it admits a
non-degenerate reflexive invariant bilinear form.
Here a form is *invariant* if it is compatible with the Lie bracket: `Φ ⁅x, y⁆ z = Φ x ⁅y, z⁆`.
-/
/-
**LieAlgebra.InvariantForm.isSemisimple_of_nondegenerate** 是 Mathlib 中的一个定理，位于命名
空间 `LieAlgebra.InvariantForm`。
形式化陈述：isSemisimple_of_nondegenerate : IsSemisimple K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `LieAlgebra.InvariantForm.atomistic`：atomistic : forall I : LieIdeal K L,
 sSup {J : LieIdeal K L | IsAtom J ∧ J <= I} = I
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用引理 `LieAlgebra.InvariantForm.orthogonal_disjoint`：orthogonal_disjoint (Φ : L
inearMap.BilinForm R L) (hΦ_nondeg : Φ.Nondegenerate) (hΦ_inv : Φ.lieInvariant L
) -- TODO: replace the following a…
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lie_eq_self_of_isAtom_of_nonabelian`：lie_eq_self_of_isAtom_of_nonabelian
 {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (I : LieIdeal R L) (hI 
: IsAtom I) (h : ¬IsLieAb…
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `LieAlgebra.InvariantForm.orthogonal_carrier`：∀ {R : Type u_1} {L : Type 
u_2} {M : Type u_3} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGr
oup M]   [inst_3 : _root_.Module …
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `LieSubmodule.mem_bot`：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ 
x = 0
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用引理 `IsAtom.disjoint_of_ne`：IsAtom.disjoint_of_ne (ha : IsAtom a) (hb : IsAto
m b) (hab : a != b) : Disjoint a b
· 使用定理 `LieSubmodule.lie_le_inf`：lie_le_inf : ⁅I, J⁆ <= I ⊓ J
· 使用定理 `LieSubmodule.lie_mem_lie`：lie_mem_lie {x : L} {m : M} (hx : x in I) (hm 
: m in N) : ⁅x, m⁆ in ⁅I, N⁆
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
A finite-dimensional Lie algebra over a field is semisimple
if it does not have non-trivial abelian ideals and it admits a
non-degenerate reflexive invariant bilinear form.
Here a form is *invariant* if it is compatible with the Lie bracket: `Φ ⁅x, y⁆ z
 = Φ x ⁅y, z⁆`.
-/
theorem isSemisimple_of_nondegenerate : IsSemisimple K L := by
  refine ⟨?_, ?_, hL⟩
  · simpa using atomistic Φ hΦ_nondeg hΦ_inv hΦ_refl hL ⊤
  intro I hI
  apply (orthogonal_disjoint Φ hΦ_nondeg hΦ_inv hL I hI).mono_right
  apply sSup_le
  simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, and_imp]
  intro J hJ hJI
  rw [← lie_eq_self_of_isAtom_of_nonabelian J hJ (hL J hJ), lieIdeal_oper_eq_span, lieSpan_le]
  rintro _ ⟨x, y, rfl⟩
  simp only [orthogonal_carrier, Set.mem_ofPred_eq]
  intro z hz
  rw [← neg_eq_zero, ← hΦ_inv]
  suffices ⁅(x : L), z⁆ = 0 by simp only [this, map_zero, LinearMap.zero_apply]
  rw [← LieSubmodule.mem_bot (R := K) (L := L), ← (hJ.disjoint_of_ne hI hJI).eq_bot]
  apply lie_le_inf
  exact lie_mem_lie x.2 hz

end field

end InvariantForm

end LieAlgebra

