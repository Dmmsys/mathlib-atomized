/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Kernel of a linear map

This file defines the kernel of a linear map.

## Main definitions

* `LinearMap.ker`: the kernel of a linear map as a submodule of the domain

## Notation

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Tags
linear algebra, vector space, module

-/

@[expose] public section

open Function
open scoped Pointwise

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}
variable {K : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {V : Type*} {V₂ : Type*}

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

/-- The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`. -/
/-
**LinearMap.ker** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：ker (f : M ->ₛₗ[τ₁₂] M₂) : Submodule R M
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is eq
uivalent to the
set of `x : M` such that `f x = 0`. The kernel is a submodule of `M`.
-/
def ker (f : M →ₛₗ[τ₁₂] M₂) : Submodule R M :=
  comap f ⊥

@[simp]
/-
**LinearMap.mem_ker** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
-/
theorem mem_ker {f : M →ₛₗ[τ₁₂] M₂} {y} : y ∈ ker f ↔ f y = 0 :=
  mem_bot R₂

@[simp]
/-
**LinearMap.ker_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_id : ker (LinearMap.id : M ->ₗ[R] M) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_id : ker (LinearMap.id : M →ₗ[R] M) = ⊥ :=
  rfl

@[simp]
/-
**LinearMap.map_coe_ker** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：map_coe_ker (f : M ->ₛₗ[τ₁₂] M₂) (x : ker f) : f x = 0
参数：f : M ->ₛₗ[τ₁₂] M₂；x : ker f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem map_coe_ker (f : M →ₛₗ[τ₁₂] M₂) (x : ker f) : f x = 0 :=
  mem_ker.1 x.2
/-
**LinearMap.ker_toAddSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_toAddSubmonoid (f : M ->ₛₗ[τ₁₂] M₂) : (ker f).toAddSubmonoid = (AddMon
oidHom.mker f)
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_toAddSubmonoid (f : M →ₛₗ[τ₁₂] M₂) : (ker f).toAddSubmonoid = (AddMonoidHom.mker f) :=
  rfl
/-
**LinearMap.le_ker_iff_comp_subtype_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
形式化陈述：le_ker_iff_comp_subtype_eq_zero {N : Submodule R M} {f : M ->ₛₗ[τ₁₂] M₂} :
 N <= ker f ↔ f ∘ₛₗ N.subtype = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LinearMap.ext_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_ker_iff_comp_subtype_eq_zero {N : Submodule R M} {f : M →ₛₗ[τ₁₂] M₂} :
    N ≤ ker f ↔ f ∘ₛₗ N.subtype = 0 := by
  rw [SetLike.le_def, LinearMap.ext_iff, Subtype.forall]; rfl
/-
**LinearMap.comp_ker_subtype** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：comp_ker_subtype (f : M ->ₛₗ[τ₁₂] M₂) : f.comp (ker f).subtype = 0
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem comp_ker_subtype (f : M →ₛₗ[τ₁₂] M₂) : f.comp (ker f).subtype = 0 :=
  LinearMap.ext fun x => mem_ker.1 x.2
/-
**LinearMap.ker_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ker (g.comp f : M ->
ₛₗ[τ₁₃] M₃) = comap f (ker g)
参数：f : M ->ₛₗ[τ₁₂] M₂；g : M₂ ->ₛₗ[τ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
    ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = comap f (ker g) :=
  rfl
/-
**LinearMap.ker_le_ker_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_le_ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ker f <= ker 
(g.comp f : M ->ₛₗ[τ₁₃] M₃)
参数：f : M ->ₛₗ[τ₁₂] M₂；g : M₂ ->ₛₗ[τ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem ker_le_ker_comp (f : M →ₛₗ[τ₁₂] M₂) (g : M₂ →ₛₗ[τ₂₃] M₃) :
    ker f ≤ ker (g.comp f : M →ₛₗ[τ₁₃] M₃) := by rw [ker_comp]; exact comap_mono bot_le
/-
**LinearMap.ker_sup_ker_le_ker_comp_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：ker_sup_ker_le_ker_comp_of_commute {f g : M ->ₗ[R] M} (h : Commute f g) : 
ker f ⊔ ker g <= ker (f ∘ₗ g)
参数：h : Commute f g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `LinearMap.ker_le_ker_comp`：ker_le_ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ 
->ₛₗ[τ₂₃] M₃) : ker f <= ker (g.comp f : M ->ₛₗ[τ₁₃] M₃)
-/
theorem ker_sup_ker_le_ker_comp_of_commute {f g : M →ₗ[R] M} (h : Commute f g) :
    ker f ⊔ ker g ≤ ker (f ∘ₗ g) := by
  refine sup_le_iff.mpr ⟨?_, ker_le_ker_comp g f⟩
  rw [← Module.End.mul_eq_comp, h.eq, Module.End.mul_eq_comp]
  exact ker_le_ker_comp f g

@[simp]
/-
**LinearMap.ker_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_le_comap {p : Submodule R₂ M₂} (f : M ->ₛₗ[τ₁₂] M₂) : ker f <= p.comap
 f
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
-/
theorem ker_le_comap {p : Submodule R₂ M₂} (f : M →ₛₗ[τ₁₂] M₂) :
    ker f ≤ p.comap f :=
  fun x hx ↦ by simp [mem_ker.mp hx]
/-
**LinearMap.disjoint_ker** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：disjoint_ker {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} : Disjoint p (ker f)
 ↔ forall x in p, f x = 0 -> x = 0
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
theorem disjoint_ker {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} :
    Disjoint p (ker f) ↔ ∀ x ∈ p, f x = 0 → x = 0 := by
  simp [disjoint_def]
/-
**LinearMap.ker_eq_bot'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ forall m, f m = 0 -> m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LinearMap.disjoint_ker`：disjoint_ker {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule
 R M} : Disjoint p (ker f) ↔ forall x in p, f x = 0 -> x = 0
-/
theorem ker_eq_bot' {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ ∀ m, f m = 0 → m = 0 := by
  simpa [disjoint_iff_inf_le] using disjoint_ker (f := f) (p := ⊤)
/-
**LinearMap.ker_eq_bot_of_inverse** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_eq_bot_of_inverse {τ₂₁ : R₂ ->+* R} [RingHomInvPair τ₁₂ τ₂₁] {f : M ->
ₛₗ[τ₁₂] M₂} {g : M₂ ->ₛₗ[τ₂₁] M} (h : (g.comp f : M ->ₗ[R] M) = id) : ker f = ⊥
参数：h : (g.comp f : M ->ₗ[R] M) = id。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.id_apply`：id_apply (x : M) : @id R M _ _ _ x = x
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
-/
theorem ker_eq_bot_of_inverse {τ₂₁ : R₂ →+* R} [RingHomInvPair τ₁₂ τ₂₁] {f : M →ₛₗ[τ₁₂] M₂}
    {g : M₂ →ₛₗ[τ₂₁] M} (h : (g.comp f : M →ₗ[R] M) = id) : ker f = ⊥ :=
  ker_eq_bot'.2 fun m hm => by rw [← id_apply (R := R) m, ← h, comp_apply, hm, g.map_zero]
/-
**LinearMap.le_ker_iff_map** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：le_ker_iff_map [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule
 R M} : p <= ker f ↔ map f p = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker.eq_1`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ 
: Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid
 M] [ins…
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Submodule.map_le_iff_le_comap`：map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} 
{p : Submodule R M} {q : Submodule R₂ M₂} : map f p <= q ↔ p <= comap f q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_ker_iff_map [RingHomSurjective τ₁₂] {f : M →ₛₗ[τ₁₂] M₂} {p : Submodule R M} :
    p ≤ ker f ↔ map f p = ⊥ := by rw [ker, eq_bot_iff, map_le_iff_le_comap]

@[simp]
/-
**LinearMap.ker_codRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_codRestrict (p : Submodule R₂ M₂) (f : M ->ₛₗ[τ₁₂] M₂) (hf) : ker (cod
Restrict p f hf) = ker f
参数：p : Submodule R₂ M₂；f : M ->ₛₗ[τ₁₂] M₂；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker.eq_1`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ 
: Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid
 M] [ins…
· 使用定理 `LinearMap.comap_codRestrict`：comap_codRestrict (p : Submodule R M) (f : 
M₂ ->ₛₗ[σ₂₁] M) (hf p') : comap (codRestrict p f hf) p' = comap f (map p.subtype
 p')
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
-/
theorem ker_codRestrict (p : Submodule R₂ M₂) (f : M →ₛₗ[τ₁₂] M₂) (hf) :
    ker (codRestrict p f hf) = ker f := by rw [ker, comap_codRestrict, Submodule.map_bot]; rfl
/-
**LinearMap.ker_domRestrict** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：ker_domRestrict (p : Submodule R M) (f : M ->ₛₗ[τ₁₂] M₂) : ker (domRestric
t f p) = (ker f).comap p.subtype
参数：p : Submodule R M；f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
-/
lemma ker_domRestrict (p : Submodule R M) (f : M →ₛₗ[τ₁₂] M₂) :
    ker (domRestrict f p) = (ker f).comap p.subtype := ker_comp ..

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.ker_restrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_restrict {p : Submodule R M} {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂
} (hf : forall x : M, x in p -> f x in q) : ker (f.restrict hf) = (ker f).comap 
p.subtype
参数：hf : forall x : M, x in p -> f x in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.restrict_eq_codRestrict_domRestrict`：restrict_eq_codRestrict_d
omRestrict {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂} (hf : 
forall x in p, f x in q) : f.restri…
· 使用定理 `LinearMap.ker_codRestrict`：ker_codRestrict (p : Submodule R₂ M₂) (f : M 
->ₛₗ[τ₁₂] M₂) (hf) : ker (codRestrict p f hf) = ker f
· 使用引理 `LinearMap.ker_domRestrict`：ker_domRestrict (p : Submodule R M) (f : M ->
ₛₗ[τ₁₂] M₂) : ker (domRestrict f p) = (ker f).comap p.subtype
-/
theorem ker_restrict {p : Submodule R M} {q : Submodule R₂ M₂} {f : M →ₛₗ[τ₁₂] M₂}
    (hf : ∀ x : M, x ∈ p → f x ∈ q) :
    ker (f.restrict hf) = (ker f).comap p.subtype := by
  rw [restrict_eq_codRestrict_domRestrict, ker_codRestrict, ker_domRestrict]

@[simp]
/-
**LinearMap.ker_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ker_zero : ker (0 : M →ₛₗ[τ₁₂] M₂) = ⊤ :=
  eq_top_iff'.2 fun x => by simp

@[simp]
/-
**LinearMap.ker_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_eq_top {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_zero`：ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
-/
theorem ker_eq_top {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 0 :=
  ⟨fun h => ext fun _ => mem_ker.1 <| h.symm ▸ trivial, fun h => h.symm ▸ ker_zero⟩

@[simp]
/-
**LinearMap.domRestrict_ker_self** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：domRestrict_ker_self (f : M ->ₛₗ[τ₁₂] M₂) : f.domRestrict f.ker = 0
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_coe_ker`：map_coe_ker (f : M ->ₛₗ[τ₁₂] M₂) (x : ker f) : f 
x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma domRestrict_ker_self (f : M →ₛₗ[τ₁₂] M₂) : f.domRestrict f.ker = 0 := by
  ext; simp
/-
**LinearMap.exists_ne_zero_of_sSup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：exists_ne_zero_of_sSup_eq_top {f : M ->ₛₗ[τ₁₂] M₂} (h : f != 0) (s : Set (
Submodule R M)) (hs : sSup s = ⊤) : exists m in s, f ∘ₛₗ m.subtype != 0
参数：h : f != 0；s : Set (Submodule R M)；hs : sSup s = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_ne_zero_of_sSup_eq_top {f : M →ₛₗ[τ₁₂] M₂} (h : f ≠ 0) (s : Set (Submodule R M))
    (hs : sSup s = ⊤) : ∃ m ∈ s, f ∘ₛₗ m.subtype ≠ 0 := by
  contrapose! h
  simp_rw [← ker_eq_top, eq_top_iff, ← hs, sSup_le_iff, le_ker_iff_comp_subtype_eq_zero]
  exact h

@[simp]
/-
**LinearMap._root_.AddMonoidHom.coe_toIntLinearMap_ker** 是 Mathlib 中的一个定理，位于命名空间
 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddMonoidHom.coe_toIntLinearMap_ker {M M₂ : Type*} [AddCommGroup M] [AddCommGroup M₂]
    (f : M →+ M₂) : LinearMap.ker f.toIntLinearMap = AddSubgroup.toIntSubmodule f.ker := rfl
/-
**LinearMap.ker_eq_bot_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_eq_bot_of_injective {f : M ->ₛₗ[τ₁₂] M₂} (hf : Injective f) : ker f = 
⊥
参数：hf : Injective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
theorem ker_eq_bot_of_injective {f : M →ₛₗ[τ₁₂] M₂} (hf : Injective f) : ker f = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simpa only [mem_ker, mem_bot, ← map_zero f, hf.eq_iff] using hx

/-- The increasing sequence of submodules consisting of the kernels of the iterates of a linear map.
-/
@[simps]
/-
**LinearMap.iterateKer** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：iterateKer (f : M ->ₗ[R] M) : Nat ->o Submodule R M where toFun n
参数：f : M ->ₗ[R] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The increasing sequence of submodules consisting of the kernels of the iterates 
of a linear map.
-/
def iterateKer (f : M →ₗ[R] M) : ℕ →o Submodule R M where
  toFun n := ker (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le w
    rw [LinearMap.mem_ker] at h
    rw [LinearMap.mem_ker, add_comm, pow_add, Module.End.mul_apply, h, map_zero]
/-
**LinearMap.ker_submoduleMap** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：ker_submoduleMap {τ₂₁ : R₂ ->+* R} [RingHomInvPair τ₁₂ τ₂₁] (f : M ->ₛₗ[τ₁
₂] M₂) (p : Submodule R M) : (f.submoduleMap p).ker = f.ker.comap p.subtype
参数：f : M ->ₛₗ[τ₁₂] M₂；p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ker_submoduleMap {τ₂₁ : R₂ →+* R} [RingHomInvPair τ₁₂ τ₂₁]
    (f : M →ₛₗ[τ₁₂] M₂) (p : Submodule R M) :
    (f.submoduleMap p).ker = f.ker.comap p.subtype := by
  ext; simp [Subtype.ext_iff]

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂}
variable {f : M →ₛₗ[τ₁₂] M₂}

open Submodule

/-
**LinearMap.ker_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : Type u_7} [inst : Ri
ng R] [inst_1 : Ring R₂]   [inst_2 : AddCommGroup M] [inst_3 : AddCommGroup M₂] 
[inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {τ₁₂ : R →+* R₂} (
f : M →ₛₗ[τ₁₂] M₂), (-f).ker = f.ker
参数：f : M →ₛₗ[τ₁₂] M₂；-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] theorem ker_neg (f : M →ₛₗ[τ₁₂] M₂) : (-f).ker = f.ker := by ext; simp
/-
**LinearMap.ker_toAddSubgroup** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_toAddSubgroup (f : M ->ₛₗ[τ₁₂] M₂) : (ker f).toAddSubgroup = f.toAddMo
noidHom.ker
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_toAddSubgroup (f : M →ₛₗ[τ₁₂] M₂) : (ker f).toAddSubgroup = f.toAddMonoidHom.ker :=
  rfl
/-
**LinearMap.sub_mem_ker_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：sub_mem_ker_iff {x y} : x - y in ker f ↔ f x = f y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sub_mem_ker_iff {x y} : x - y ∈ ker f ↔ f x = f y := by rw [mem_ker, map_sub, sub_eq_zero]
/-
**LinearMap.disjoint_ker_iff_injOn** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：disjoint_ker_iff_injOn {p : Submodule R M} : Disjoint p (LinearMap.ker f) 
↔ Set.InjOn f p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.disjoint_ker`：disjoint_ker {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule
 R M} : Disjoint p (ker f) ↔ forall x in p, f x = 0 -> x = 0
· 使用定理 `Set.injOn_iff_map_eq_zero`：∀ {F : Type u_3} {G : Type u_4} {H : Type u_5
} {S : Type u_6} [inst : AddGroup G] [inst_1 : AddGroup H]   [inst_2 : FunLike F
 G H] [AddMonoi…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem disjoint_ker_iff_injOn {p : Submodule R M} :
    Disjoint p (LinearMap.ker f) ↔ Set.InjOn f p := by
  rw [disjoint_ker, Set.injOn_iff_map_eq_zero]
/-
**LinearMap.injOn_of_disjoint_ker** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：injOn_of_disjoint_ker {p : Submodule R M} {s : Set M} (h : s subseteq p) (
hd : Disjoint p (ker f)) : Set.InjOn f s
参数：h : s subseteq p；hd : Disjoint p (ker f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f : α →
 β}, s₁ ⊆ s₂ → Set.InjOn f s₂ → Set.InjOn f s₁
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.disjoint_ker_iff_injOn`：disjoint_ker_iff_injOn {p : Submodule 
R M} : Disjoint p (LinearMap.ker f) ↔ Set.InjOn f p
-/
theorem injOn_of_disjoint_ker {p : Submodule R M} {s : Set M} (h : s ⊆ p)
    (hd : Disjoint p (ker f)) : Set.InjOn f s :=
  disjoint_ker_iff_injOn.mp hd |>.mono h
/-
**LinearMap.ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LinearMap.disjoint_ker_iff_injOn`：disjoint_ker_iff_injOn {p : Submodule 
R M} : Disjoint p (LinearMap.ker f) ↔ Set.InjOn f p
-/
theorem ker_eq_bot {f : M →ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Injective f := by
  simpa [disjoint_iff_inf_le] using disjoint_ker_iff_injOn (f := f) (p := ⊤)
/-
**LinearMap.injective_domRestrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : Type u_7} [inst : Ri
ng R] [inst_1 : Ring R₂]   [inst_2 : AddCommGroup M] [inst_3 : AddCommGroup M₂] 
[inst_4 : _root_.Module R M] [inst_5 : _root_.Module R₂ M₂]   {τ₁₂ : R →+* R₂} {
f : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M}, Function.Injective ⇑(f.domRestrict S) ↔ 
Disjoint S f.ker
参数：f.domRestrict S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LinearMap.ker_domRestrict`：ker_domRestrict (p : Submodule R M) (f : M ->
ₛₗ[τ₁₂] M₂) : ker (domRestrict f p) = (ker f).comap p.subtype
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma injective_domRestrict_iff {f : M →ₛₗ[τ₁₂] M₂} {S : Submodule R M} :
    Injective (f.domRestrict S) ↔ Disjoint S f.ker := by
  simp [← ker_eq_bot, ker_domRestrict, disjoint_iff_comap_eq_bot]

@[simp]
/-
**LinearMap.injective_restrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：injective_restrict_iff {p : Submodule R M} {q : Submodule R₂ M₂} {f : M ->
ₛₗ[τ₁₂] M₂} (hf : forall x in p, f x in q) : Injective (f.restrict hf) ↔ Disjoin
t p (ker f)
参数：hf : forall x in p, f x in q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.ker_restrict`：ker_restrict {p : Submodule R M} {q : Submodule 
R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂} (hf : forall x : M, x in p -> f x in q) : ker (f.res
trict hf) = …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem injective_restrict_iff {p : Submodule R M} {q : Submodule R₂ M₂} {f : M →ₛₗ[τ₁₂] M₂}
    (hf : ∀ x ∈ p, f x ∈ q) : Injective (f.restrict hf) ↔ Disjoint p (ker f) := by
  simp [← ker_eq_bot, ker_restrict, disjoint_iff_comap_eq_bot]

@[deprecated (since := "2026-07-01")]
alias injective_restrict_iff_disjoint := injective_restrict_iff

@[simp]
/-
**LinearMap.injective_codRestrict_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：injective_codRestrict_iff {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂} (hf :
 forall x, f x in q) : Injective (f.codRestrict q hf) ↔ Injective f
参数：hf : forall x, f x in q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.injective_codRestrict`：injective_codRestrict {f : ι -> α} {s : Set α
} (h : forall x, f x in s) : Injective (codRestrict f s h) ↔ Injective f
-/
theorem injective_codRestrict_iff {q : Submodule R₂ M₂} {f : M →ₛₗ[τ₁₂] M₂}
    (hf : ∀ x, f x ∈ q) : Injective (f.codRestrict q hf) ↔ Injective f :=
  Set.injective_codRestrict _

end Ring

section CommSemiring

variable [Semiring R] [CommSemiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R →+* R₂}

/-
**LinearMap.ker_le_ker_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_le_ker_smul (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂) : ker f <= ker (c • f)
参数：f : M ->ₛₗ[τ₁₂] M₂；c : R₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_le_comap_smul`：comap_le_comap_smul (f : M ->ₛₗ[τ₁₂] M₂) 
(c : R₂) : comap f q <= comap (c • f) q
-/
theorem ker_le_ker_smul (f : M →ₛₗ[τ₁₂] M₂) (c : R₂) : ker f ≤ ker (c • f) := by
  simpa only [ker] using Submodule.comap_le_comap_smul _ _ _

end CommSemiring

section Semifield

variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

/-
**LinearMap.ker_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_smul (f : V ->ₗ[K] V₂) (a : K) (h : a != 0) : ker (a • f) = ker f
参数：f : V ->ₗ[K] V₂；a : K；h : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_smul`：comap_smul (f : V ->ₗ[K] V₂) (p : Submodule K V₂) 
(a : K) (h : a != 0) : p.comap (a • f) = p.comap f
-/
theorem ker_smul (f : V →ₗ[K] V₂) (a : K) (h : a ≠ 0) : ker (a • f) = ker f :=
  Submodule.comap_smul f _ a h
/-
**LinearMap.ker_smul'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_smul' (f : V ->ₗ[K] V₂) (a : K) : ker (a • f) = ⨅ _ : a != 0, ker f
参数：f : V ->ₗ[K] V₂；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.comap_smul'`：comap_smul' (f : V ->ₗ[K] V₂) (p : Submodule K V₂
) (a : K) : p.comap (a • f) = ⨅ _ : a != 0, p.comap f
-/
theorem ker_smul' (f : V →ₗ[K] V₂) (a : K) : ker (a • f) = ⨅ _ : a ≠ 0, ker f :=
  Submodule.comap_smul' f _ a

end Semifield

end LinearMap

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable (p : Submodule R M)
variable {τ₁₂ : R →+* R₂}

open LinearMap

@[simp]
/-
**Submodule.comap_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
参数：f : M ->ₛₗ[τ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_bot (f : M →ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f :=
  rfl

@[simp]
/-
**Submodule.ker_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_subtype : ker p.subtype = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem ker_subtype : ker p.subtype = ⊥ :=
  ker_eq_bot_of_injective fun _ _ => Subtype.ext

@[simp]
/-
**Submodule.ker_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：ker_inclusion (p p' : Submodule R M) (h : p <= p') : ker (inclusion h) = ⊥
参数：p p' : Submodule R M；h : p <= p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.inclusion.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {p p' : Submodul
e R M} (h : p …
· 使用定理 `LinearMap.ker_codRestrict`：ker_codRestrict (p : Submodule R₂ M₂) (f : M 
->ₛₗ[τ₁₂] M₂) (hf) : ker (codRestrict p f hf) = ker f
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
-/
theorem ker_inclusion (p p' : Submodule R M) (h : p ≤ p') : ker (inclusion h) = ⊥ := by
  rw [inclusion, ker_codRestrict, ker_subtype]

end AddCommMonoid

end Submodule

namespace LinearMap

section Semiring

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R →+* R₂} {τ₂₃ : R₂ →+* R₃} {τ₁₃ : R →+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

/-
**LinearMap.ker_comp_of_ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_comp_of_ker_eq_bot (f : M ->ₛₗ[τ₁₂] M₂) {g : M₂ ->ₛₗ[τ₂₃] M₃} (hg : ke
r g = ⊥) : ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = ker f
参数：f : M ->ₛₗ[τ₁₂] M₂；hg : ker g = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `Submodule.comap_bot`：comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f
-/
theorem ker_comp_of_ker_eq_bot (f : M →ₛₗ[τ₁₂] M₂) {g : M₂ →ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) :
    ker (g.comp f : M →ₛₗ[τ₁₃] M₃) = ker f := by rw [ker_comp, hg, Submodule.comap_bot]

end Semiring

section RestrictScalars

variable (R : Type*) {S M N : Type*} [Semiring R] [Semiring S] [SMul R S]
variable [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

@[simp]
/-
**LinearMap.ker_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ker_restrictScalars (f : M ->ₗ[S] N) : ker (f.restrictScalars R) = (ker f)
.restrictScalars R
参数：f : M ->ₗ[S] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
theorem ker_restrictScalars (f : M →ₗ[S] N) :
    ker (f.restrictScalars R) = (ker f).restrictScalars R :=
  rfl

end RestrictScalars

end LinearMap

/-! ### Linear equivalences -/


namespace LinearEquiv

section AddCommMonoid

section

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
variable {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable {σ₃₂ : R₃ →+* R₂}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}
variable (e : M ≃ₛₗ[σ₁₂] M₂) (e'' : M₂ ≃ₛₗ[σ₂₃] M₃)

@[simp]
/-
**LinearEquiv.ker** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : Type u_7} [inst : Se
miring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M] [inst_3 : AddCommM
onoid M₂] {module_M : _root_.Module R M}   {module_M₂ : _root_.Module R₂ M₂} {σ₁
₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} {re₁₂ : RingHomInvPair σ₁₂ σ₂₁}   {re₂₁ : RingHom
InvPair σ₂₁ σ₁₂} (e : M ≃ₛₗ[σ₁₂] M₂), (↑e).ker = ⊥
参数：e : M ≃ₛₗ[σ₁₂] M₂；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem ker : LinearMap.ker (e : M →ₛₗ[σ₁₂] M₂) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective e.toEquiv.injective

@[simp]
/-
**LinearEquiv.ker_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：ker_comp (l : M ->ₛₗ[σ₁₂] M₂) : LinearMap.ker (((e'' : M₂ ->ₛₗ[σ₂₃] M₃).co
mp l : M ->ₛₗ[σ₁₃] M₃) : M ->ₛₗ[σ₁₃] M₃) = LinearMap.ker l
参数：l : M ->ₛₗ[σ₁₂] M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ker_comp_of_ker_eq_bot`：ker_comp_of_ker_eq_bot (f : M ->ₛₗ[τ₁₂
] M₂) {g : M₂ ->ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) : ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) =
 ker f
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
-/
theorem ker_comp (l : M →ₛₗ[σ₁₂] M₂) :
    LinearMap.ker (((e'' : M₂ →ₛₗ[σ₂₃] M₃).comp l : M →ₛₗ[σ₁₃] M₃) : M →ₛₗ[σ₁₃] M₃) =
    LinearMap.ker l :=
  LinearMap.ker_comp_of_ker_eq_bot _ e''.ker

end

end AddCommMonoid

end LinearEquiv

