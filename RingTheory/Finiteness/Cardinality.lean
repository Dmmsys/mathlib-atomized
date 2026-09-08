/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Module.Congruence.Defs
public import Mathlib.LinearAlgebra.Basis.Cardinality
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite modules and types with finitely many elements

This file relates `Module.Finite` and `_root_.Finite`.

-/

@[expose] public section

open Function (Surjective)
open Finsupp

section ModuleAndAlgebra

variable (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

open Module in
/-
**Submodule.fg_iff_exists_fin_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.fg_iff_exists_fin_linearMap {N : Submodule R M} : N.FG ↔ exists 
(n : Nat) (f : (Fin n -> R) ->ₗ[R] M), LinearMap.range f = N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.exists_congr_right`：∀ {α : Sort u} {β : Sort v} {q : β → Prop} (e 
: α ≃ β), (∃ a, q (e a)) ↔ ∃ b, q b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.constr_range`：constr_range {f : ι -> M'} : LinearMap.range 
(constr (M'
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Submodule.fg_iff_exists_fin_linearMap {N : Submodule R M} :
    N.FG ↔ ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), LinearMap.range f = N := by
  simp_rw [fg_iff_exists_fin_generating_family, ← ((Pi.basisFun R _).constr ℕ).exists_congr_right]
  simp [Basis.constr_range]
/-
**AddSubmonoid.fg_iff_exists_fin_addMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubmonoid.fg_iff_exists_fin_addMonoidHom {M : Type*} [AddCommMonoid M] 
{S : AddSubmonoid M} : S.FG ↔ exists (n : Nat) (f : (Fin n -> Nat) ->+ M), AddMo
noidHom.mrange f = S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubmonoid.toNatSubmodule_toAddSubmonoid`：AddSubmonoid.toNatSubmodule_
toAddSubmonoid (S : AddSubmonoid M) : S.toNatSubmodule.toAddSubmonoid = S
· 使用定理 `Submodule.fg_iff_addSubmonoid_fg`：fg_iff_addSubmonoid_fg (P : Submodule 
Nat M) : P.FG ↔ P.toAddSubmonoid.FG
· 使用定理 `Submodule.fg_iff_exists_fin_linearMap`：Submodule.fg_iff_exists_fin_linea
rMap {N : Submodule R M} : N.FG ↔ exists (n : Nat) (f : (Fin n -> R) ->ₗ[R] M), 
LinearMap.range f = N
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.range_toAddSubmonoid`：range_toAddSubmonoid [RingHomSurjective 
τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : (range f).toAddSubmonoid = AddMonoidHom.mrange f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.toAddSubmonoid_inj`：toAddSubmonoid_inj : p.toAddSubmonoid = q.
toAddSubmonoid ↔ p = q
-/
theorem AddSubmonoid.fg_iff_exists_fin_addMonoidHom {M : Type*} [AddCommMonoid M]
    {S : AddSubmonoid M} : S.FG ↔ ∃ (n : ℕ) (f : (Fin n → ℕ) →+ M), AddMonoidHom.mrange f = S := by
  rw [← S.toNatSubmodule_toAddSubmonoid, ← Submodule.fg_iff_addSubmonoid_fg,
    Submodule.fg_iff_exists_fin_linearMap]
  exact exists_congr fun n => ⟨fun ⟨f, hf⟩ => ⟨f, hf ▸ LinearMap.range_toAddSubmonoid _⟩,
    fun ⟨f, hf⟩ => ⟨f.toNatLinearMap, Submodule.toAddSubmonoid_inj.mp <|
      hf ▸ LinearMap.range_toAddSubmonoid _⟩⟩
/-
**AddSubgroup.fg_iff_exists_fin_addMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AddSubgroup.fg_iff_exists_fin_addMonoidHom {M : Type*} [AddCommGroup M] {H
 : AddSubgroup M} : H.FG ↔ exists (n : Nat) (f : (Fin n -> Int) ->+ M), AddMonoi
dHom.range f = H
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubgroup.toIntSubmodule_toAddSubgroup`：AddSubgroup.toIntSubmodule_toA
ddSubgroup (S : AddSubgroup M) : S.toIntSubmodule.toAddSubgroup = S
· 使用定理 `Submodule.fg_iff_addSubgroup_fg`：fg_iff_addSubgroup_fg {G : Type*} [AddC
ommGroup G] (P : Submodule Int G) : P.FG ↔ P.toAddSubgroup.FG
· 使用定理 `Submodule.fg_iff_exists_fin_linearMap`：Submodule.fg_iff_exists_fin_linea
rMap {N : Submodule R M} : N.FG ↔ exists (n : Nat) (f : (Fin n -> R) ->ₗ[R] M), 
LinearMap.range f = N
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.range_toAddSubgroup`：range_toAddSubgroup [RingHomSurjective τ₁
₂] (f : M ->ₛₗ[τ₁₂] M₂) : (range f).toAddSubgroup = f.toAddMonoidHom.range
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.toAddSubmonoid_inj`：toAddSubmonoid_inj : p.toAddSubmonoid = q.
toAddSubmonoid ↔ p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem AddSubgroup.fg_iff_exists_fin_addMonoidHom {M : Type*} [AddCommGroup M]
    {H : AddSubgroup M} : H.FG ↔ ∃ (n : ℕ) (f : (Fin n → ℤ) →+ M), AddMonoidHom.range f = H := by
  rw [← H.toIntSubmodule_toAddSubgroup, ← Submodule.fg_iff_addSubgroup_fg,
    Submodule.fg_iff_exists_fin_linearMap]
  refine exists_congr fun n => ⟨fun ⟨f, hf⟩ => ⟨f, hf ▸ LinearMap.range_toAddSubgroup _⟩,
    fun ⟨f, hf⟩ => ⟨f.toIntLinearMap, Submodule.toAddSubmonoid_inj.mp ?_⟩⟩
  simp [hf]

namespace Module

namespace Finite

open Submodule Set

/-- A finite module admits a surjective linear map from a finite free module. -/
/-
**Module.Finite.exists_fin'** 是 Mathlib 中的一个引理，位于命名空间 `Module.Finite`。
形式化陈述：exists_fin' [Module.Finite R M] : exists (n : Nat) (f : (Fin n -> R) ->ₗ[R
] M), Surjective f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_iff_exists_fin_linearMap`：Submodule.fg_iff_exists_fin_linea
rMap {N : Submodule R M} : N.FG ↔ exists (n : Nat) (f : (Fin n -> R) ->ₗ[R] M), 
LinearMap.range f = N
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f

--- 原说明 ---
A finite module admits a surjective linear map from a finite free module.
-/
lemma exists_fin' [Module.Finite R M] : ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Surjective f :=
  have ⟨n, f, hf⟩ := (Submodule.fg_iff_exists_fin_linearMap R M).mp fg_top
  ⟨n, f, by rw [← LinearMap.range_eq_top, hf]⟩

/-- A finite module can be realised as a quotient of `Fin n → R` (i.e. `R^n`). -/
/-
**Module.Finite.exists_fin_quot_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Module.Finite`。
形式化陈述：exists_fin_quot_equiv (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
 [Module.Finite R M] : exists (n : Nat) (S : Submodule R (Fin n -> R)), Nonempty
 ((_ ⧸ S) ≃ₗ[R] M)
参数：R M : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f

--- 原说明 ---
A finite module can be realised as a quotient of `Fin n → R` (i.e. `R^n`).
-/
theorem exists_fin_quot_equiv (R M : Type*) [Ring R] [AddCommGroup M] [Module R M]
      [Module.Finite R M] :
    ∃ (n : ℕ) (S : Submodule R (Fin n → R)), Nonempty ((_ ⧸ S) ≃ₗ[R] M) :=
  let ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  ⟨n, LinearMap.ker f, ⟨f.quotKerEquivOfSurjective hf⟩⟩

variable {M}
/-
**Module.Finite._root_.Module.finite_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Module
.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Module.finite_of_finite [Finite R] [Module.Finite R M] : Finite M := by
  obtain ⟨n, f, hf⟩ := exists_fin' R M; exact .of_surjective f hf

variable {R}

/-- A module over a finite ring has finite dimension iff it is finite. -/
/-
**Module.Finite._root_.Module.finite_iff_finite** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module over a finite ring has finite dimension iff it is finite.
-/
lemma _root_.Module.finite_iff_finite [Finite R] : Module.Finite R M ↔ Finite M :=
  ⟨fun _ ↦ finite_of_finite R, fun _ ↦ .of_finite⟩

variable (R) in
/-
**Module.Finite._root_.Set.Finite.submoduleSpan** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e.Finite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Set.Finite.submoduleSpan [Finite R] {s : Set M} (hs : s.Finite) :
    (Submodule.span R s : Set M).Finite := by
  lift s to Finset M using hs
  rw [Set.Finite, ← Module.finite_iff_finite (R := R)]
  dsimp
  infer_instance

/-- If a free module is finite, then any arbitrary basis is finite. -/
/-
**Module.Finite.finite_basis** 是 Mathlib 中的一个引理，位于命名空间 `Module.Finite`。
形式化陈述：finite_basis [Nontrivial R] {ι} [Module.Finite R M] (b : Basis ι R M) : _r
oot_.Finite ι
参数：b : Basis ι R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `basis_finite_of_finite_spans`：basis_finite_of_finite_spans [Nontrivial R
] {s : Set M} (hs : s.Finite) (hsspan : span R s = ⊤) {ι : Type w} (b : Basis ι 
R M) : Finite ι
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite

--- 原说明 ---
If a free module is finite, then any arbitrary basis is finite.
-/
lemma finite_basis [Nontrivial R] {ι} [Module.Finite R M]
    (b : Basis ι R M) :
    _root_.Finite ι :=
  let ⟨s, hs⟩ := ‹Module.Finite R M›
  basis_finite_of_finite_spans s.finite_toSet hs b

end Finite

variable {R M}
/-
**Module.not_finite_of_infinite_basis** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：not_finite_of_infinite_basis [Nontrivial R] {ι} [Infinite ι] (b : Basis ι 
R M) : ¬ Module.Finite R M
参数：b : Basis ι R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.not_infinite`：∀ {α : Sort u_1}, Finite α → ¬Infinite α
· 使用引理 `Module.Finite.finite_basis`：finite_basis [Nontrivial R] {ι} [Module.Fini
te R M] (b : Basis ι R M) : _root_.Finite ι
-/
lemma not_finite_of_infinite_basis [Nontrivial R] {ι} [Infinite ι] (b : Basis ι R M) :
    ¬ Module.Finite R M :=
  fun _ ↦ (Finite.finite_basis b).not_infinite ‹_›

end Module

end ModuleAndAlgebra

namespace Module.Finite

universe u
variable (R : Type u) (M : Type*)

section Ring

variable [Ring R] [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- The kernel of a random surjective linear map from a finite free module
to a given finite module. -/
/-
**Module.Finite.kerRepr** 是 Mathlib 中的一个定义，位于命名空间 `Module.Finite`。
形式化陈述：kerRepr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a random surjective linear map from a finite free module
to a given finite module.
-/
noncomputable def kerRepr := LinearMap.ker (Finite.exists_fin' R M).choose_spec.choose

/-- A representative of a finite module in the same universe as the ring. -/
/-
**Module.Finite.repr** 是 Mathlib 中的一个定义，位于命名空间 `Module.Finite`。
形式化陈述：(R : Type u) →   (M : Type u_1) →     [inst : Ring R] → [inst_1 : AddCommG
roup M] → [inst_2 : _root_.Module R M] → [Module.Finite R M] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A representative of a finite module in the same universe as the ring.
-/
protected abbrev repr : Type u := _ ⧸ kerRepr R M

/-- The representative is isomorphic to the original module. -/
/-
**Module.Finite.reprEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Finite`。
形式化陈述：reprEquiv : Finite.repr R M ≃ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representative is isomorphic to the original module.
-/
noncomputable def reprEquiv : Finite.repr R M ≃ₗ[R] M :=
  LinearMap.quotKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

end Ring

section Semiring

variable [Semiring R] [AddCommMonoid M] [Module R M] [Module.Finite R M]

/-- The kernel (as a congruence relation) of a random surjective linear map
from a finite free module to a given finite module. -/
/-
**Module.Finite.kerRepr** 是 Mathlib 中的一个定义，位于命名空间 `Module.Finite`。
形式化陈述：kerRepr
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel (as a congruence relation) of a random surjective linear map
from a finite free module to a given finite module.
-/
noncomputable def kerReprₛ :=
  ModuleCon.ker (Finite.exists_fin' R M).choose_spec.choose.toDistribMulActionHom

/-- A representative of a finite module in the same universe as the semiring. -/
/-
**Module.Finite.repr** 是 Mathlib 中的一个定义，位于命名空间 `Module.Finite`。
形式化陈述：(R : Type u) →   (M : Type u_1) →     [inst : Ring R] → [inst_1 : AddCommG
roup M] → [inst_2 : _root_.Module R M] → [Module.Finite R M] → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A representative of a finite module in the same universe as the semiring.
-/
protected abbrev reprₛ : Type u := (kerReprₛ R M).Quotient

/-- The representative is isomorphic to the original module. -/
/-
**Module.Finite.reprEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Module.Finite`。
形式化陈述：reprEquiv : Finite.repr R M ≃ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representative is isomorphic to the original module.
-/
noncomputable def reprEquivₛ : Finite.reprₛ R M ≃ₗ[R] M :=
  ModuleCon.quotientKerEquivOfSurjective _ (Finite.exists_fin' R M).choose_spec.choose_spec

end Semiring

end Module.Finite

