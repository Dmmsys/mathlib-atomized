/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.RepresentationTheory.Basic

/-!
# Invariant submodules of a group representation

-/

@[expose] public section

open scoped MonoidAlgebra

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]
  (ρ : Representation k G V)

namespace Representation

/-- Given a representation `ρ` of a group, `ρ.invtSubmodule` is the sublattice of all
`ρ`-invariant submodules. -/
/-
**Representation.invtSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：invtSubmodule : Sublattice (Submodule k V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a representation `ρ` of a group, `ρ.invtSubmodule` is the sublattice of al
l
`ρ`-invariant submodules.
-/
def invtSubmodule : Sublattice (Submodule k V) :=
  ⨅ g, Module.End.invtSubmodule (ρ g)
/-
**Representation.mem_invtSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `Representation`。
形式化陈述：mem_invtSubmodule {p : Submodule k V} : p in ρ.invtSubmodule ↔ forall g, p
 in Module.End.invtSubmodule (ρ g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Representation.invtSubmodule.eq_1`：∀ {k : Type u_1} {G : Type u_2} {V : 
Type u_3} [inst : CommSemiring k] [inst_1 : Monoid G] [inst_2 : AddCommMonoid V]
   [inst_3 : _root_.Mod…
· 使用定理 `Sublattice.mem_iInf`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Lattice α] 
{a : α} {f : ι → Sublattice α}, a ∈ ⨅ i, f i ↔ ∀ (i : ι), a ∈ f i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_invtSubmodule {p : Submodule k V} :
    p ∈ ρ.invtSubmodule ↔ ∀ g, p ∈ Module.End.invtSubmodule (ρ g) := by
  rw [invtSubmodule, Sublattice.mem_iInf]

namespace invtSubmodule

/-
**Representation.invtSubmodule.top_mem** 是 Mathlib 中的一个定理，位于命名空间 `Representation
.invtSubmodule`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module k V] (ρ : 
Representation k G V), ⊤ ∈ ρ.invtSubmodule
参数：ρ : Representation k G V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] protected lemma top_mem : ⊤ ∈ ρ.invtSubmodule := by simp [invtSubmodule]
/-
**Representation.invtSubmodule.bot_mem** 是 Mathlib 中的一个定理，位于命名空间 `Representation
.invtSubmodule`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module k V] (ρ : 
Representation k G V), ⊥ ∈ ρ.invtSubmodule
参数：ρ : Representation k G V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] protected lemma bot_mem : ⊥ ∈ ρ.invtSubmodule := by simp [invtSubmodule]
/-
**Representation.invtSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.invtSu
bmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder ρ.invtSubmodule where
  top := ⟨⊤, invtSubmodule.top_mem ρ⟩
  bot := ⟨⊥, invtSubmodule.bot_mem ρ⟩
  le_top := fun ⟨p, hp⟩ ↦ by simp
  bot_le := fun ⟨p, hp⟩ ↦ by simp
/-
**Representation.invtSubmodule.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `Representation
.invtSubmodule`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module k V] (ρ : 
Representation k G V), ↑⊤ = ⊤
参数：ρ : Representation k G V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected lemma coe_top : (↑(⊤ : ρ.invtSubmodule) : Submodule k V) = ⊤ := rfl
/-
**Representation.invtSubmodule.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `Representation
.invtSubmodule`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module k V] (ρ : 
Representation k G V), ↑⊥ = ⊥
参数：ρ : Representation k G V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] protected lemma coe_bot : (↑(⊥ : ρ.invtSubmodule) : Submodule k V) = ⊥ := rfl
/-
**Representation.invtSubmodule.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `Represe
ntation.invtSubmodule`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid V]   [inst_3 : _root_.Module k V] (ρ : 
Representation k G V), Nontrivial ↥ρ.invtSubmodule ↔ Nontrivial V
参数：ρ : Representation k G V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `Representation.invtSubmodule.coe_top`：∀ {k : Type u_1} {G : Type u_2} {V
 : Type u_3} [inst : CommSemiring k] [inst_1 : Monoid G] [inst_2 : AddCommMonoid
 V]   [inst_3 : _root_.Mod…
· 使用定理 `Representation.invtSubmodule.coe_bot`：∀ {k : Type u_1} {G : Type u_2} {V
 : Type u_3} [inst : CommSemiring k] [inst_1 : Monoid G] [inst_2 : AddCommMonoid
 V]   [inst_3 : _root_.Mod…
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
-/
protected lemma nontrivial_iff : Nontrivial ρ.invtSubmodule ↔ Nontrivial V := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    infer_instance
  · refine ⟨⊥, ⊤, ?_⟩
    rw [← Subtype.coe_ne_coe, invtSubmodule.coe_top, invtSubmodule.coe_bot]
    exact bot_ne_top
/-
**Representation.invtSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `Representation.invtSu
bmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial V] : Nontrivial ρ.invtSubmodule :=
  (invtSubmodule.nontrivial_iff ρ).mpr inferInstance

end invtSubmodule

set_option backward.isDefEq.respectTransparency false in
/-
**Representation.asAlgebraHom_mem_of_forall_mem** 是 Mathlib 中的一个引理，位于命名空间 `Repre
sentation`。
形式化陈述：asAlgebraHom_mem_of_forall_mem (p : Submodule k V) (hp : forall g, forall 
v in p, ρ g v in p) (v : V) (hv : v in p) (x : k[G]) : ρ.asAlgebraHom x v in p
参数：p : Submodule k V；hp : forall g, forall v in p, ρ g v in p；v : V；hv : v in p；
x : k[G]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidAlgebra.induction_on`：induction_on {motive : R[M] -> Prop} (x : R[
M]) (of : forall m, motive (.of R M m)) (add : forall x y : R[M], motive x -> mo
tive y -> motive…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidAlgebra.of_apply`：∀ (R : Type u_8) (M : Type u_9) [inst : Semiring
 R] [inst_1 : MulOneClass M] (a : M),   (MonoidAlgebra.of R M) a = MonoidAlgebra
.single a 1
· 使用定理 `Representation.asAlgebraHom_single`：asAlgebraHom_single (g : G) (r : k) 
: asAlgebraHom ρ (MonoidAlgebra.single g r) = r • ρ g
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
-/
lemma asAlgebraHom_mem_of_forall_mem (p : Submodule k V) (hp : ∀ g, ∀ v ∈ p, ρ g v ∈ p)
    (v : V) (hv : v ∈ p) (x : k[G]) :
    ρ.asAlgebraHom x v ∈ p := by
  apply x.induction_on <;> aesop

/-- The natural order isomorphism between the two ways to represent invariant submodules. -/
/-
**Representation.mapSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Representation`。
形式化陈述：mapSubmodule : ρ.invtSubmodule ≃o Submodule k[G] ρ.asModule where toFun p
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Representation.instIsScalarTowerMonoidAlgebraAsModule`：∀ {k : Type u_1} 
{G : Type u_2} {V : Type u_3} [inst : CommSemiring k] [inst_1 : Monoid G] [inst_
2 : AddCommMonoid V]   [inst_3 : _root_.Mod…

--- 原说明 ---
The natural order isomorphism between the two ways to represent invariant submod
ules.
-/
noncomputable def mapSubmodule : ρ.invtSubmodule ≃o Submodule k[G] ρ.asModule where
  toFun p :=
    { toAddSubmonoid := (p : Submodule k V).toAddSubmonoid.map ρ.asModuleEquiv.symm
      smul_mem' := by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          AddSubmonoid.mem_map, Submodule.mem_toAddSubmonoid, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂]
        refine fun x v hv ↦ ⟨ρ.asModuleEquiv (x • ρ.asModuleEquiv.symm v), ?_, rfl⟩
        simpa using ρ.asAlgebraHom_mem_of_forall_mem p (ρ.mem_invtSubmodule.mp p.property) v hv x }
  invFun q := ⟨(Submodule.orderIsoMapComap ρ.asModuleEquiv.symm).symm (q.restrictScalars k), by
    rw [invtSubmodule, Sublattice.mem_iInf]
    intro g v hv
    simp only [Submodule.orderIsoMapComap_symm_apply, Submodule.mem_comap] at hv ⊢
    convert! q.smul_mem (MonoidAlgebra.of k G g) hv using 1
    rw [LinearEquiv.coe_coe, ← asModuleEquiv_symm_map_rho]⟩
  left_inv p := by ext; simp
  right_inv q := by ext; aesop
  map_rel_iff' {p q} :=
    ⟨fun h x hx ↦ by
      suffices ρ.asModuleEquiv.symm x ∈
        (q : Submodule k V).toAddSubmonoid.map ρ.asModuleEquiv.symm by simpa using this
      exact h <| by simpa using hx,
    fun h x hx ↦ by aesop⟩

end Representation

