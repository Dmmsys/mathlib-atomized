/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Jacobson radical of modules and rings

## Main definitions

`Module.jacobson R M`: the Jacobson radical of a module `M` over a ring `R` is defined to be the
intersection of all maximal submodules of `M`.

`Ring.jacobson R`: the Jacobson radical of a ring `R` is the Jacobson radical of `R` as
an `R`-module, which is equal to the intersection of all maximal left ideals of `R`. It turns out
it is in fact a two-sided ideal, and equals the intersection of all maximal right ideals of `R`.

## Reference
* [F. Lorenz, *Algebra: Volume II: Fields with Structure, Algebras and Advanced Topics*][Lorenz2008]
-/

@[expose] public section

assert_not_exists Cardinal

namespace Module

open Submodule

variable (R R₂ M M₂ : Type*) [Ring R] [Ring R₂]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₂] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂} [RingHomSurjective τ₁₂]
variable (f : M →ₛₗ[τ₁₂] M₂)

/-- The Jacobson radical of an `R`-module `M` is the infimum of all maximal submodules in `M`. -/
/-
**Module.jacobson** 是 Mathlib 中的一个定义，位于命名空间 `Module`。
形式化陈述：jacobson : Submodule R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Jacobson radical of an `R`-module `M` is the infimum of all maximal submodul
es in `M`.
-/
def jacobson : Submodule R M :=
  sInf { m : Submodule R M | IsCoatom m }

variable {R R₂ M M₂}
/-
**Module.le_comap_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：le_comap_jacobson : jacobson R M <= comap f (jacobson R₂ M₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.jacobson.eq_1`：∀ (R : Type u_1) (M : Type u_3) [inst : Ring R] [i
nst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   Module.jacobson R M = sI
nf {m | Is…
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `Submodule.comap_iInf`：comap_iInf {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι
 -> Submodule R₂ M₂) : comap f (⨅ i, p i) = ⨅ i, comap f (p i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `Submodule.isCoatom_comap_or_eq_top`：isCoatom_comap_or_eq_top (f : M ->ₛₗ
[τ₁₂] M₂) {p : Submodule R₂ M₂} (hp : IsCoatom p) : IsCoatom (comap f p) ∨ comap
 f p = ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sInf`：mem_sInf {S : Set (Submodule R M)} {x : M} : x in sI
nf S ↔ forall p in S, x in p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
-/
theorem le_comap_jacobson : jacobson R M ≤ comap f (jacobson R₂ M₂) := by
  conv_rhs => rw [jacobson, sInf_eq_iInf', comap_iInf]
  refine le_iInf_iff.mpr fun S m hm ↦ ?_
  obtain h | h := isCoatom_comap_or_eq_top f S.2
  · exact mem_sInf.mp hm _ h
  · simpa only [h] using mem_top
/-
**Module.map_jacobson_le** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：map_jacobson_le : map f (jacobson R M) <= jacobson R₂ M₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Module.le_comap_jacobson`：le_comap_jacobson : jacobson R M <= comap f (j
acobson R₂ M₂)
-/
theorem map_jacobson_le : map f (jacobson R M) ≤ jacobson R₂ M₂ :=
  map_le_iff_le_comap.mpr (le_comap_jacobson f)
/-
**Module.jacobson_eq_bot_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：jacobson_eq_bot_of_injective (inj : Function.Injective f) (h : jacobson R₂
 M₂ = ⊥) : jacobson R M = ⊥
参数：inj : Function.Injective f；h : jacobson R₂ M₂ = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Module.le_comap_jacobson`：le_comap_jacobson : jacobson R M <= comap f (j
acobson R₂ M₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
-/
theorem jacobson_eq_bot_of_injective (inj : Function.Injective f) (h : jacobson R₂ M₂ = ⊥) :
    jacobson R M = ⊥ :=
  le_bot_iff.mp <| (le_comap_jacobson f).trans <| by
    simp_rw [h, comap_bot, (LinearMap.ker_eq_bot.mpr inj).le]

variable {f}
/-
**Module.map_jacobson_of_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：map_jacobson_of_ker_le (surj : Function.Surjective f) (le : LinearMap.ker 
f <= jacobson R M) : map f (jacobson R M) = jacobson R₂ M₂
参数：surj : Function.Surjective f；le : LinearMap.ker f <= jacobson R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Module.map_jacobson_le`：map_jacobson_le : map f (jacobson R M) <= jacobs
on R₂ M₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.jacobson.eq_1`：∀ (R : Type u_1) (M : Type u_3) [inst : Ring R] [i
nst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   Module.jacobson R M = sI
nf {m | Is…
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `Submodule.map_iInf_of_ker_le`：map_iInf_of_ker_le {f : M ->ₛₗ[τ₁₂] M₂} (h
f : Surjective f) {ι} {p : ι -> Submodule R M} (h : LinearMap.ker f <= ⨅ i, p i)
 : map f (⨅ i, p i…
· 使用定理 `le_iInf`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] {f :
 ι → α} {a : α}, (∀ (i : ι), a ≤ f i) → a ≤ iInf f
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Submodule.isCoatom_map_of_ker_le`：isCoatom_map_of_ker_le {f : M ->ₛₗ[τ₁₂
] M₂} (hf : Surjective f) {p : Submodule R M} (le : LinearMap.ker f <= p) (hp : 
IsCoatom p) : IsCoatom…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iInf_iff`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] 
{f : ι → α} {a : α}, a ≤ iInf f ↔ ∀ (i : ι), a ≤ f i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem map_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f ≤ jacobson R M) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
  le_antisymm (map_jacobson_le f) <| by
    rw [jacobson, sInf_eq_iInf'] at le
    conv_rhs => rw [jacobson, sInf_eq_iInf', map_iInf_of_ker_le surj le]
    exact le_iInf fun m ↦ sInf_le (isCoatom_map_of_ker_le surj (le_iInf_iff.mp le m) m.2)
/-
**Module.comap_jacobson_of_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：comap_jacobson_of_ker_le (surj : Function.Surjective f) (le : LinearMap.ke
r f <= jacobson R M) : comap f (jacobson R₂ M₂) = jacobson R M
参数：surj : Function.Surjective f；le : LinearMap.ker f <= jacobson R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.map_jacobson_of_ker_le`：map_jacobson_of_ker_le (surj : Function.S
urjective f) (le : LinearMap.ker f <= jacobson R M) : map f (jacobson R M) = jac
obson R₂ M₂
· 使用定理 `Submodule.comap_map_eq_self`：comap_map_eq_self {f : M ->ₛₗ[τ₁₂] M₂} {p :
 Submodule R M} (h : LinearMap.ker f <= p) : comap f (map f p) = p
-/
theorem comap_jacobson_of_ker_le (surj : Function.Surjective f)
    (le : LinearMap.ker f ≤ jacobson R M) :
    comap f (jacobson R₂ M₂) = jacobson R M := by
  rw [← map_jacobson_of_ker_le surj le, comap_map_eq_self le]
/-
**Module.map_jacobson_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：map_jacobson_of_bijective (hf : Function.Bijective f) : map f (jacobson R 
M) = jacobson R₂ M₂
参数：hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.map_jacobson_of_ker_le`：map_jacobson_of_ker_le (surj : Function.S
urjective f) (le : LinearMap.ker f <= jacobson R M) : map f (jacobson R M) = jac
obson R₂ M₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem map_jacobson_of_bijective (hf : Function.Bijective f) :
    map f (jacobson R M) = jacobson R₂ M₂ :=
  map_jacobson_of_ker_le hf.2 <| by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]
/-
**Module.comap_jacobson_of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：comap_jacobson_of_bijective (hf : Function.Bijective f) : comap f (jacobso
n R₂ M₂) = jacobson R M
参数：hf : Function.Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.comap_jacobson_of_ker_le`：comap_jacobson_of_ker_le (surj : Functi
on.Surjective f) (le : LinearMap.ker f <= jacobson R M) : comap f (jacobson R₂ M
₂) = jacobson R M
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem comap_jacobson_of_bijective (hf : Function.Bijective f) :
    comap f (jacobson R₂ M₂) = jacobson R M :=
  comap_jacobson_of_ker_le hf.2 <| by simp_rw [LinearMap.ker_eq_bot.mpr hf.1, bot_le]
/-
**Module.jacobson_quotient_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：jacobson_quotient_of_le {N : Submodule R M} (le : N <= jacobson R M) : jac
obson R (M ⧸ N) = map N.mkQ (jacobson R M)
参数：le : N <= jacobson R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.map_jacobson_of_ker_le`：map_jacobson_of_ker_le (surj : Function.S
urjective f) (le : LinearMap.ker f <= jacobson R M) : map f (jacobson R M) = jac
obson R₂ M₂
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
-/
theorem jacobson_quotient_of_le {N : Submodule R M} (le : N ≤ jacobson R M) :
    jacobson R (M ⧸ N) = map N.mkQ (jacobson R M) :=
  (map_jacobson_of_ker_le N.mkQ_surjective <| by rwa [ker_mkQ]).symm
/-
**Module.jacobson_le_of_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：jacobson_le_of_eq_bot {N : Submodule R M} (h : jacobson R (M ⧸ N) = ⊥) : j
acobson R M <= N
参数：h : jacobson R (M ⧸ N) = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem jacobson_le_of_eq_bot {N : Submodule R M} (h : jacobson R (M ⧸ N) = ⊥) :
    jacobson R M ≤ N := by
  simp_rw [← N.ker_mkQ, ← comap_bot, ← h, le_comap_jacobson]

variable (R M)

@[simp]
/-
**Module.jacobson_quotient_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：jacobson_quotient_jacobson : jacobson R (M ⧸ jacobson R M) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.jacobson_quotient_of_le`：jacobson_quotient_of_le {N : Submodule R
 M} (le : N <= jacobson R M) : jacobson R (M ⧸ N) = map N.mkQ (jacobson R M)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Submodule.mkQ_map_self`：mkQ_map_self : map p.mkQ p = ⊥
-/
theorem jacobson_quotient_jacobson : jacobson R (M ⧸ jacobson R M) = ⊥ := by
  rw [jacobson_quotient_of_le le_rfl, mkQ_map_self]
/-
**Module.jacobson_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：jacobson_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] : jacobson R M
 < ⊤
参数：Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsCoatomic.eq_top_or_exists_le_coatom`：∀ {α : Type u_2} {inst : PartialO
rder α} {inst_1 : OrderTop α} [self : IsCoatomic α] (b : α),   b = ⊤ ∨ ∃ a, IsCo
atom a ∧ b ≤ a
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem jacobson_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] : jacobson R M < ⊤ := by
  obtain ⟨m, hm, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule R M)).resolve_left bot_ne_top
  exact (sInf_le <| Set.mem_ofPred.mpr hm).trans_lt hm.1.lt_top
/-
**Module.** 是 Mathlib 中的一个示例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Nontrivial M] [Module.Finite R M] : jacobson R M < ⊤ := jacobson_lt_top R M

variable {ι} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
/-
**Module.jacobson_pi_le** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：jacobson_pi_le : jacobson R (Π i, M i) <= Submodule.pi Set.univ (jacobson 
R <| M ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sInf_eq_iInf'`：∀ {α : Type u_1} [inst : InfSet α] (s : Set α), sInf s = 
⨅ a, ↑a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.comap_iInf`：comap_iInf {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι
 -> Submodule R₂ M₂) : comap f (⨅ i, p i) = ⨅ i, comap f (p i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iInf_le_of_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α
] {f : ι → α} {a : α} (i : ι), f i ≤ a → iInf f ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.isCoatom_comap_iff`：isCoatom_comap_iff {f : M ->ₛₗ[τ₁₂] M₂} (h
f : Surjective f) {p : Submodule R₂ M₂} : IsCoatom (comap f p) ↔ IsCoatom p
· 使用定理 `LinearMap.proj_surjective`：proj_surjective (i : ι) : Surjective (proj i 
: ((i : ι) -> φ i) ->ₗ[R] φ i)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem jacobson_pi_le : jacobson R (Π i, M i) ≤ Submodule.pi Set.univ (jacobson R <| M ·) := by
  simp_rw [← iInf_comap_proj, jacobson, sInf_eq_iInf', comap_iInf, le_iInf_iff]
  intro i m
  exact iInf_le_of_le ⟨_, (isCoatom_comap_iff <| LinearMap.proj_surjective i).mpr m.2⟩ le_rfl

/-- A product of modules with trivial Jacobson radical (e.g. simple modules) also has trivial
Jacobson radical. -/
/-
**Module.jacobson_pi_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：jacobson_pi_eq_bot (h : forall i, jacobson R (M i) = ⊥) : jacobson R (Π i,
 M i) = ⊥
参数：h : forall i, jacobson R (M i) = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Module.jacobson_pi_le`：jacobson_pi_le : jacobson R (Π i, M i) <= Submodu
le.pi Set.univ (jacobson R <| M ·)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.pi_univ_bot`：pi_univ_bot : (pi Set.univ fun i : ι => (⊥ : Subm
odule R (φ i))) = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
A product of modules with trivial Jacobson radical (e.g. simple modules) also ha
s trivial
Jacobson radical.
-/
theorem jacobson_pi_eq_bot (h : ∀ i, jacobson R (M i) = ⊥) : jacobson R (Π i, M i) = ⊥ :=
  le_bot_iff.mp <| (jacobson_pi_le R M).trans <| by simp_rw [h, pi_univ_bot, le_rfl]

end Module

section

variable (R R₂ : Type*) [Ring R] [Ring R₂] (f : R →+* R₂) [RingHomSurjective f]
variable (M : Type*) [AddCommGroup M] [Module R M]

namespace Ring

/-- The Jacobson radical of a ring `R` is the Jacobson radical of `R` as an `R`-module. -/
-- TODO: replace all `Ideal.jacobson ⊥` by this.
/-
**Ring.jacobson** 是 Mathlib 中的一个缩写定义，位于命名空间 `Ring`。
形式化陈述：jacobson : Ideal R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev jacobson : Ideal R := Module.jacobson R R
/-
**Ring.jacobson_eq_sInf_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：jacobson_eq_sInf_isMaximal : jacobson R = sInf {I : Ideal R | I.IsMaximal}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem jacobson_eq_sInf_isMaximal : jacobson R = sInf {I : Ideal R | I.IsMaximal} := by
  simp_rw [jacobson, Module.jacobson, Ideal.isMaximal_def]
/-
**Ring.** 是 Mathlib 中的一个实例，位于命名空间 `Ring`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (jacobson R).IsTwoSided :=
  ⟨fun b ha ↦ Module.le_comap_jacobson (f := LinearMap.toSpanSingleton R R b) ha⟩

variable {R R₂}
/-
**Ring.jacobson_le_of_isMaximal** 是 Mathlib 中的一个引理，位于命名空间 `Ring`。
形式化陈述：jacobson_le_of_isMaximal (m : Ideal R) [m.IsMaximal] : jacobson R <= m
参数：m : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.jacobson_eq_sInf_isMaximal`：jacobson_eq_sInf_isMaximal : jacobson R
 = sInf {I : Ideal R | I.IsMaximal}
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
lemma jacobson_le_of_isMaximal (m : Ideal R) [m.IsMaximal] : jacobson R ≤ m := by
  rw [Ring.jacobson_eq_sInf_isMaximal]
  exact sInf_le ‹_›
/-
**Ring.le_comap_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：le_comap_jacobson : jacobson R <= Ideal.comap f (jacobson R₂)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.le_comap_jacobson`：le_comap_jacobson : jacobson R M <= comap f (j
acobson R₂ M₂)
-/
theorem le_comap_jacobson : jacobson R ≤ Ideal.comap f (jacobson R₂) :=
  Module.le_comap_jacobson f.toSemilinearMap
/-
**Ring.map_jacobson_le** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：map_jacobson_le : Submodule.map f.toSemilinearMap (jacobson R) <= jacobson
 R₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.map_jacobson_le`：map_jacobson_le : map f (jacobson R M) <= jacobs
on R₂ M₂
-/
theorem map_jacobson_le : Submodule.map f.toSemilinearMap (jacobson R) ≤ jacobson R₂ :=
  Module.map_jacobson_le f.toSemilinearMap

variable {f} in
/-
**Ring.map_jacobson_of_ker_le** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：map_jacobson_of_ker_le (le : RingHom.ker f <= jacobson R) : Submodule.map 
f.toSemilinearMap (jacobson R) = jacobson R₂
参数：le : RingHom.ker f <= jacobson R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.map_jacobson_of_ker_le`：map_jacobson_of_ker_le (surj : Function.S
urjective f) (le : LinearMap.ker f <= jacobson R M) : map f (jacobson R M) = jac
obson R₂ M₂
· 使用定理 `RingHom.surjective`：RingHom.surjective (σ : R₁ ->+* R₂) [t : RingHomSurj
ective σ] : Function.Surjective σ
-/
theorem map_jacobson_of_ker_le (le : RingHom.ker f ≤ jacobson R) :
    Submodule.map f.toSemilinearMap (jacobson R) = jacobson R₂ :=
  Module.map_jacobson_of_ker_le f.surjective le
/-
**Ring.coe_jacobson_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：coe_jacobson_quotient (I : Ideal R) [I.IsTwoSided] : (jacobson (R ⧸ I) : S
et (R ⧸ I)) = Module.jacobson R (R ⧸ I)
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.jacobson.eq_1`：∀ (R : Type u_1) [inst : Ring R], Ring.jacobson R = 
Module.jacobson R R
· 使用定理 `Ideal.Quotient.instRingHomSurjectiveQuotientMk`：∀ {R : Type u} [inst : R
ing R] {I : Ideal R} [inst_1 : I.IsTwoSided], RingHomSurjective (Ideal.Quotient.
mk I)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.map_jacobson_of_ker_le`：map_jacobson_of_ker_le (surj : Function.S
urjective f) (le : LinearMap.ker f <= jacobson R M) : map f (jacobson R M) = jac
obson R₂ M₂
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem coe_jacobson_quotient (I : Ideal R) [I.IsTwoSided] :
    (jacobson (R ⧸ I) : Set (R ⧸ I)) = Module.jacobson R (R ⧸ I) := by
  let f : R ⧸ I →ₛₗ[Ideal.Quotient.mk I] R ⧸ I := ⟨AddHom.id _, fun _ _ ↦ rfl⟩
  rw [jacobson, ← Module.map_jacobson_of_ker_le (f := f) Function.surjective_id]
  · apply Set.image_id
  · rintro _ rfl; exact zero_mem _
/-
**Ring.jacobson_quotient_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：jacobson_quotient_of_le {I : Ideal R} [I.IsTwoSided] (le : I <= jacobson R
) : jacobson (R ⧸ I) = Submodule.map (Ideal.Quotient.mk I).toSemilinearMap (jaco
bson R)
参数：le : I <= jacobson R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.Quotient.instRingHomSurjectiveQuotientMk`：∀ {R : Type u} [inst : R
ing R] {I : Ideal R} [inst_1 : I.IsTwoSided], RingHomSurjective (Ideal.Quotient.
mk I)
· 使用定理 `Module.map_jacobson_of_ker_le`：map_jacobson_of_ker_le (surj : Function.S
urjective f) (le : LinearMap.ker f <= jacobson R M) : map f (jacobson R M) = jac
obson R₂ M₂
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
-/
theorem jacobson_quotient_of_le {I : Ideal R} [I.IsTwoSided] (le : I ≤ jacobson R) :
    jacobson (R ⧸ I) = Submodule.map (Ideal.Quotient.mk I).toSemilinearMap (jacobson R) :=
  .symm <| Module.map_jacobson_of_ker_le (by exact Ideal.Quotient.mk_surjective) <| by
    rwa [← I.ker_mkQ] at le
/-
**Ring.jacobson_le_of_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：jacobson_le_of_eq_bot {I : Ideal R} [I.IsTwoSided] (h : jacobson (R ⧸ I) =
 ⊥) : jacobson R <= I
参数：h : jacobson (R ⧸ I) = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.jacobson_le_of_eq_bot`：jacobson_le_of_eq_bot {N : Submodule R M} 
(h : jacobson R (M ⧸ N) = ⊥) : jacobson R M <= N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Ring.coe_jacobson_quotient`：coe_jacobson_quotient (I : Ideal R) [I.IsTwo
Sided] : (jacobson (R ⧸ I) : Set (R ⧸ I)) = Module.jacobson R (R ⧸ I)
-/
theorem jacobson_le_of_eq_bot {I : Ideal R} [I.IsTwoSided] (h : jacobson (R ⧸ I) = ⊥) :
    jacobson R ≤ I :=
  Module.jacobson_le_of_eq_bot <| by
    rw [← le_bot_iff, ← SetLike.coe_subset_coe] at h ⊢
    rwa [← coe_jacobson_quotient]

variable (R)

@[simp]
/-
**Ring.jacobson_quotient_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：jacobson_quotient_jacobson : jacobson (R ⧸ jacobson R) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ring.instIsTwoSidedJacobson`：∀ (R : Type u_1) [inst : Ring R], (Ring.jac
obson R).IsTwoSided
· 使用定理 `Ideal.Quotient.instRingHomSurjectiveQuotientMk`：∀ {R : Type u} [inst : R
ing R] {I : Ideal R} [inst_1 : I.IsTwoSided], RingHomSurjective (Ideal.Quotient.
mk I)
· 使用定理 `Ring.jacobson_quotient_of_le`：jacobson_quotient_of_le {I : Ideal R} [I.I
sTwoSided] (le : I <= jacobson R) : jacobson (R ⧸ I) = Submodule.map (Ideal.Quot
ient.mk I).toSemil…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Submodule.mkQ_map_self`：mkQ_map_self : map p.mkQ p = ⊥
-/
theorem jacobson_quotient_jacobson : jacobson (R ⧸ jacobson R) = ⊥ :=
  (jacobson_quotient_of_le le_rfl).trans <| SetLike.ext' <| by
    apply SetLike.ext'_iff.mp (jacobson R).mkQ_map_self
/-
**Ring.jacobson_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：jacobson_lt_top [Nontrivial R] : jacobson R < ⊤
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.jacobson_lt_top`：jacobson_lt_top [Nontrivial M] [IsCoatomic (Subm
odule R M)] : jacobson R M < ⊤
· 使用定理 `Ideal.instIsCoatomic`：∀ {α : Type u} [inst : Semiring α], IsCoatomic (Id
eal α)
-/
theorem jacobson_lt_top [Nontrivial R] : jacobson R < ⊤ := Module.jacobson_lt_top R R
/-
**Ring.jacobson_smul_top_le** 是 Mathlib 中的一个定理，位于命名空间 `Ring`。
形式化陈述：jacobson_smul_top_le : jacobson R • (⊤ : Submodule R M) <= Module.jacobson
 R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `Module.le_comap_jacobson`：le_comap_jacobson : jacobson R M <= comap f (j
acobson R₂ M₂)
-/
theorem jacobson_smul_top_le : jacobson R • (⊤ : Submodule R M) ≤ Module.jacobson R M :=
  Submodule.smul_le.mpr fun _ hr m _ ↦ Module.le_comap_jacobson (LinearMap.toSpanSingleton R M m) hr

end Ring

namespace Submodule

variable {R M}

/-
**Submodule.jacobson_smul_lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：jacobson_smul_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] (N : Subm
odule R M) : Ring.jacobson R • N < ⊤
参数：Submodule R M；N : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `smul_mono_right`：smul_mono_right [SMul M α] [Preorder α] [CovariantClass
 M α HSMul.hSMul LE.le] (m : M) : Monotone (HSMul.hSMul m : α -> α)
· 使用定理 `Submodule.instCovariantClassHSMulLe_1`：∀ {R : Type u} [inst : Semiring R
] {A : Type v} [inst_1 : Semiring A] [inst_2 : _root_.Module R A] {M : Type u_1}
   [inst_3 : AddCommMonoid …
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Ring.jacobson_smul_top_le`：jacobson_smul_top_le : jacobson R • (⊤ : Subm
odule R M) <= Module.jacobson R M
· 使用定理 `Module.jacobson_lt_top`：jacobson_lt_top [Nontrivial M] [IsCoatomic (Subm
odule R M)] : jacobson R M < ⊤
-/
theorem jacobson_smul_lt_top [Nontrivial M] [IsCoatomic (Submodule R M)] (N : Submodule R M) :
    Ring.jacobson R • N < ⊤ :=
  ((smul_mono_right _ le_top).trans <| Ring.jacobson_smul_top_le R M).trans_lt
    (Module.jacobson_lt_top R M)
/-
**Submodule.FG.jacobson_smul_lt** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_3} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {N : Submodule R M}, N ≠ ⊥ → N.FG → Ring.jacobson
 R • N < N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.map_strictMono_of_injective`：map_strictMono_of_injective : Str
ictMono (map f)
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Submodule.jacobson_smul_lt_top`：jacobson_smul_lt_top [Nontrivial M] [IsC
oatomic (Submodule R M)] (N : Submodule R M) : Ring.jacobson R • N < ⊤
· 使用定理 `Submodule.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot : Nontrivial p ↔ 
p != ⊥
· 使用定理 `Module.Finite.instIsCoatomicSubmodule`：∀ {R : Type u_1} {M : Type u_4} [
inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mo
dule.Finite R M], IsCoatomi…
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
-/
theorem FG.jacobson_smul_lt {N : Submodule R M} (ne_bot : N ≠ ⊥) (fg : N.FG) :
    Ring.jacobson R • N < N := by
  rw [← Module.Finite.iff_fg] at fg
  rw [← nontrivial_iff_ne_bot] at ne_bot
  convert! map_strictMono_of_injective N.injective_subtype (jacobson_smul_lt_top ⊤)
  on_goal 1 => rw [map_smul'']
  all_goals rw [Submodule.map_top, range_subtype]

/-- A form of Nakayama's lemma for modules over noncommutative rings. -/
/-
**Submodule.FG.eq_bot_of_le_jacobson_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.F
G`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {M : Type u_3} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {N : Submodule R M}, N.FG → N ≤ Ring.jacobson R •
 N → N = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Submodule.FG.jacobson_smul_lt`：∀ {R : Type u_1} [inst : Ring R] {M : Typ
e u_3} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {N : Submodule R
 M}, N ≠ ⊥ → N.FG →…

--- 原说明 ---
A form of Nakayama's lemma for modules over noncommutative rings.
-/
theorem FG.eq_bot_of_le_jacobson_smul {N : Submodule R M} (fg : N.FG)
    (le : N ≤ Ring.jacobson R • N) : N = ⊥ := by
  contrapose! le; exact (jacobson_smul_lt le fg).not_ge

end Submodule

end

