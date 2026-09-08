/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov, Kim Morrison
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.Algebra.Ring.Opposite
public import Mathlib.Data.Finsupp.Basic

/-!
# Monoid algebras and the opposite ring
-/

assert_not_exists NonUnitalAlgHom AlgEquiv

@[expose] public noncomputable section

open Finsupp MulOpposite

variable {R M : Type*} [Semiring R] [Mul M]

namespace MonoidAlgebra

/-- The opposite of a monoid algebra is equivalent as a ring to the opposite monoid algebra over the
opposite ring. -/
@[to_additive (dont_translate := R) (attr := simps! +simpRhs apply symm_apply)
/-- The opposite of a monoid algebra is equivalent as a ring to the opposite monoid algebra over the
opposite ring. -/]
/-
**MonoidAlgebra.opRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MonoidAlgebra`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} → [inst : Semiring R] → [inst_1 : Mul M]
 → (MonoidAlgebra R M)ᵐᵒᵖ ≃+* MonoidAlgebra Rᵐᵒᵖ Mᵐᵒᵖ
参数：MonoidAlgebra R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected noncomputable def opRingEquiv : R[M]ᵐᵒᵖ ≃+* Rᵐᵒᵖ[Mᵐᵒᵖ] where
  toAddEquiv :=
    opAddEquiv.symm.trans <| (mapDomainAddEquiv _ opEquiv).trans <| mapAddEquiv _ opAddEquiv
  map_mul' := by
    classical
    simp [coeff_mul, MonoidAlgebra.ext_iff, Finsupp.ext_iff, ← MulOpposite.unop_inj,
      unop_finsuppSum, sum_mapRange_index, apply_ite unop, mapAddEquiv]
    simpa using fun _ _ _ ↦ Finsupp.sum_comm ..

@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.opRingEquiv_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra`。
形式化陈述：opRingEquiv_single (r : R) (x : M) : MonoidAlgebra.opRingEquiv (op (single
 x r)) = single (op x) (op r)
参数：r : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidAlgebra.opRingEquiv_apply`：∀ {R : Type u_1} {M : Type u_2} [inst :
 Semiring R] [inst_1 : Mul M] (a : (MonoidAlgebra R M)ᵐᵒᵖ),   MonoidAlgebra.opRi
ngEquiv a =     (Mono…
· 使用引理 `MonoidAlgebra.mapDomainAddEquiv_single`：mapDomainAddEquiv_single (e : M 
≃ N) (r : R) (m : M) : mapDomainAddEquiv R e (single m r) = single (e m) r
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulOpposite.opEquiv_apply`：∀ {α : Type u_1}, ⇑MulOpposite.opEquiv = MulO
pposite.op
· 使用引理 `MonoidAlgebra.mapAddEquiv_single`：mapAddEquiv_single (e : R ≃+ S) (r : R
) (m : M) : mapAddEquiv M e (single m r) = single m (e r)
· 使用定理 `MulOpposite.opAddEquiv_apply`：∀ {α : Type u_2} [inst : Add α], ⇑MulOppos
ite.opAddEquiv = MulOpposite.op
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opRingEquiv_single (r : R) (x : M) :
    MonoidAlgebra.opRingEquiv (op (single x r)) = single (op x) (op r) := by ext; simp

@[to_additive (dont_translate := R)]
/-
**MonoidAlgebra.opRingEquiv_symm_single** 是 Mathlib 中的一个引理，位于命名空间 `MonoidAlgebra
`。
形式化陈述：opRingEquiv_symm_single (r : Rᵐᵒᵖ) (x : Mᵐᵒᵖ) : MonoidAlgebra.opRingEquiv.
symm (single x r) = op (single x.unop r.unop)
参数：r : Rᵐᵒᵖ；x : Mᵐᵒᵖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulOpposite.unop_injective`：unop_injective : Injective (unop : αᵐᵒᵖ -> α
)
· 使用定理 `MonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R] {
x y : MonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MonoidAlgebra.opRingEquiv_symm_apply`：∀ {R : Type u_1} {M : Type u_2} [i
nst : Semiring R] [inst_1 : Mul M] (a : MonoidAlgebra Rᵐᵒᵖ Mᵐᵒᵖ),   MonoidAlgebr
a.opRingEquiv.symm a =    …
· 使用引理 `MonoidAlgebra.mapAddEquiv_single`：mapAddEquiv_single (e : R ≃+ S) (r : R
) (m : M) : mapAddEquiv M e (single m r) = single m (e r)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `MulOpposite.opAddEquiv_symm_apply`：∀ {α : Type u_2} [inst : Add α], ⇑Mul
Opposite.opAddEquiv.symm = MulOpposite.unop
· 使用引理 `MonoidAlgebra.mapDomainAddEquiv_single`：mapDomainAddEquiv_single (e : M 
≃ N) (r : R) (m : M) : mapDomainAddEquiv R e (single m r) = single (e m) r
· 使用定理 `MulOpposite.opEquiv_symm_apply`：∀ {α : Type u_1}, ⇑MulOpposite.opEquiv.s
ymm = MulOpposite.unop
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma opRingEquiv_symm_single (r : Rᵐᵒᵖ) (x : Mᵐᵒᵖ) :
    MonoidAlgebra.opRingEquiv.symm (single x r) = op (single x.unop r.unop) := by
  apply MulOpposite.unop_injective; ext; simp

end MonoidAlgebra

