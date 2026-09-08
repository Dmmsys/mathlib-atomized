/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Data.DFinsupp.Module
public import Mathlib.Data.Finsupp.SMul

/-!
# Conversion between `Finsupp` and homogeneous `DFinsupp`

This module provides conversions between `Finsupp` and `DFinsupp`.
It is in its own file since neither `Finsupp` or `DFinsupp` depend on each other.

## Main definitions

* "identity" maps between `Finsupp` and `DFinsupp`:
  * `Finsupp.toDFinsupp : (ι →₀ M) → (Π₀ i : ι, M)`
  * `DFinsupp.toFinsupp : (Π₀ i : ι, M) → (ι →₀ M)`
  * Bundled equiv versions of the above:
    * `finsuppEquivDFinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M)`
    * `finsuppAddEquivDFinsupp : (ι →₀ M) ≃+ (Π₀ i : ι, M)`
    * `finsuppLequivDFinsupp R : (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M)`
* stronger versions of `Finsupp.split`:
  * `sigmaFinsuppEquivDFinsupp : ((Σ i, η i) →₀ N) ≃ (Π₀ i, (η i →₀ N))`
  * `sigmaFinsuppAddEquivDFinsupp : ((Σ i, η i) →₀ N) ≃+ (Π₀ i, (η i →₀ N))`
  * `sigmaFinsuppLequivDFinsupp : ((Σ i, η i) →₀ N) ≃ₗ[R] (Π₀ i, (η i →₀ N))`

## Theorems

The defining features of these operations is that they preserve the function and support:

* `Finsupp.toDFinsupp_coe`
* `Finsupp.toDFinsupp_support`
* `DFinsupp.toFinsupp_coe`
* `DFinsupp.toFinsupp_support`

and therefore map `Finsupp.single` to `DFinsupp.single` and vice versa:

* `Finsupp.toDFinsupp_single`
* `DFinsupp.toFinsupp_single`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to `Finsupp.toDFinsupp`:

* `finsupp_add_equiv_dfinsupp_apply`
* `finsupp_lequiv_dfinsupp_apply`
* `finsupp_add_equiv_dfinsupp_symm_apply`
* `finsupp_lequiv_dfinsupp_symm_apply`

## Implementation notes

We provide `DFinsupp.toFinsupp` and `finsuppEquivDFinsupp` computably by adding
`[DecidableEq ι]` and `[Π m : M, Decidable (m ≠ 0)]` arguments. To aid with definitional unfolding,
these arguments are also present on the `noncomputable` equivs.
-/

@[expose] public section


variable {ι : Type*} {R : Type*} {M : Type*}

/-! ### Basic definitions and lemmas -/


section Defs

/-- Interpret a `Finsupp` as a homogeneous `DFinsupp`. -/
/-
**Finsupp.toDFinsupp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Finsupp.toDFinsupp [Zero M] (f : ι ->₀ M) : Π₀ _ : ι, M where toFun
参数：f : ι ->₀ M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a `Finsupp` as a homogeneous `DFinsupp`.
-/
def Finsupp.toDFinsupp [Zero M] (f : ι →₀ M) : Π₀ _ : ι, M where
  toFun := f
  support' :=
    Trunc.mk
      ⟨f.support.1, fun i => (Classical.em (f i = 0)).symm.imp_left Finsupp.mem_support_iff.mpr⟩

@[simp]
/-
**Finsupp.toDFinsupp_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.toDFinsupp_coe [Zero M] (f : ι ->₀ M) : ⇑f.toDFinsupp = f
参数：f : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finsupp.toDFinsupp_coe [Zero M] (f : ι →₀ M) : ⇑f.toDFinsupp = f :=
  rfl

section

variable [DecidableEq ι] [Zero M]

@[simp]
/-
**Finsupp.toDFinsupp_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.toDFinsupp_single (i : ι) (m : M) : (Finsupp.single i m).toDFinsup
p = DFinsupp.single i m
参数：i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Finsupp.toDFinsupp_single (i : ι) (m : M) :
    (Finsupp.single i m).toDFinsupp = DFinsupp.single i m := by
  ext
  simp [Finsupp.single_apply, DFinsupp.single_apply]

variable [∀ m : M, Decidable (m ≠ 0)]

@[simp]
/-
**toDFinsupp_support** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toDFinsupp_support (f : ι ->₀ M) : f.toDFinsupp.support = f.support
参数：f : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toDFinsupp_support (f : ι →₀ M) : f.toDFinsupp.support = f.support := by
  ext
  simp

/-- Interpret a homogeneous `DFinsupp` as a `Finsupp`.

Note that the elaborator has a lot of trouble with this definition - it is often necessary to
write `(DFinsupp.toFinsupp f : ι →₀ M)` instead of `f.toFinsupp`, as for some unknown reason
using dot notation or omitting the type ascription prevents the type being resolved correctly. -/
/-
**DFinsupp.toFinsupp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DFinsupp.toFinsupp (f : Π₀ _ : ι, M) : ι ->₀ M
参数：f : Π₀ _ : ι, M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret a homogeneous `DFinsupp` as a `Finsupp`.

Note that the elaborator has a lot of trouble with this definition - it is often
 necessary to
write `(DFinsupp.toFinsupp f : ι →₀ M)` instead of `f.toFinsupp`, as for some un
known reason
using dot notation or omitting the type ascription prevents the type being resol
ved correctly.
-/
def DFinsupp.toFinsupp (f : Π₀ _ : ι, M) : ι →₀ M :=
  ⟨f.support, f, fun i => by simp only [DFinsupp.mem_support_iff]⟩

@[simp]
/-
**DFinsupp.toFinsupp_coe** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DFinsupp.toFinsupp_coe (f : Π₀ _ : ι, M) : ⇑f.toFinsupp = f
参数：f : Π₀ _ : ι, M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem DFinsupp.toFinsupp_coe (f : Π₀ _ : ι, M) : ⇑f.toFinsupp = f :=
  rfl

@[simp]
/-
**DFinsupp.toFinsupp_support** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DFinsupp.toFinsupp_support (f : Π₀ _ : ι, M) : f.toFinsupp.support = f.sup
port
参数：f : Π₀ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem DFinsupp.toFinsupp_support (f : Π₀ _ : ι, M) : f.toFinsupp.support = f.support := by
  ext
  simp

@[simp]
/-
**DFinsupp.toFinsupp_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DFinsupp.toFinsupp_single (i : ι) (m : M) : (DFinsupp.single i m : Π₀ _ : 
ι, M).toFinsupp = Finsupp.single i m
参数：i : ι；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem DFinsupp.toFinsupp_single (i : ι) (m : M) :
    (DFinsupp.single i m : Π₀ _ : ι, M).toFinsupp = Finsupp.single i m := by
  ext
  simp [Finsupp.single_apply, DFinsupp.single_apply]

@[simp]
/-
**Finsupp.toDFinsupp_toFinsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finsupp.toDFinsupp_toFinsupp (f : ι ->₀ M) : f.toDFinsupp.toFinsupp = f
参数：f : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem Finsupp.toDFinsupp_toFinsupp (f : ι →₀ M) : f.toDFinsupp.toFinsupp = f :=
  DFunLike.coe_injective rfl

@[simp]
/-
**DFinsupp.toFinsupp_toDFinsupp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DFinsupp.toFinsupp_toDFinsupp (f : Π₀ _ : ι, M) : f.toFinsupp.toDFinsupp =
 f
参数：f : Π₀ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem DFinsupp.toFinsupp_toDFinsupp (f : Π₀ _ : ι, M) : f.toFinsupp.toDFinsupp = f :=
  DFunLike.coe_injective rfl

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace Finsupp

@[simp]
/-
**Finsupp.toDFinsupp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toDFinsupp_zero [Zero M] : (0 : ι ->₀ M).toDFinsupp = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem toDFinsupp_zero [Zero M] : (0 : ι →₀ M).toDFinsupp = 0 :=
  DFunLike.coe_injective rfl

@[simp]
/-
**Finsupp.toDFinsupp_add** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toDFinsupp_add [AddZeroClass M] (f g : ι ->₀ M) : (f + g).toDFinsupp = f.t
oDFinsupp + g.toDFinsupp
参数：f g : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem toDFinsupp_add [AddZeroClass M] (f g : ι →₀ M) :
    (f + g).toDFinsupp = f.toDFinsupp + g.toDFinsupp :=
  DFunLike.coe_injective rfl

@[simp]
/-
**Finsupp.toDFinsupp_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toDFinsupp_neg [AddGroup M] (f : ι ->₀ M) : (-f).toDFinsupp = -f.toDFinsup
p
参数：f : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem toDFinsupp_neg [AddGroup M] (f : ι →₀ M) : (-f).toDFinsupp = -f.toDFinsupp :=
  DFunLike.coe_injective rfl

@[simp]
/-
**Finsupp.toDFinsupp_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toDFinsupp_sub [AddGroup M] (f g : ι ->₀ M) : (f - g).toDFinsupp = f.toDFi
nsupp - g.toDFinsupp
参数：f g : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem toDFinsupp_sub [AddGroup M] (f g : ι →₀ M) :
    (f - g).toDFinsupp = f.toDFinsupp - g.toDFinsupp :=
  DFunLike.coe_injective rfl

@[simp]
/-
**Finsupp.toDFinsupp_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toDFinsupp_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] (r : R) (f
 : ι ->₀ M) : (r • f).toDFinsupp = r • f.toDFinsupp
参数：r : R；f : ι ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem toDFinsupp_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] (r : R) (f : ι →₀ M) :
    (r • f).toDFinsupp = r • f.toDFinsupp :=
  DFunLike.coe_injective rfl

end Finsupp

namespace DFinsupp

variable [DecidableEq ι]

@[simp]
/-
**DFinsupp.toFinsupp_zero** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toFinsupp_zero [Zero M] [forall m : M, Decidable (m != 0)] : toFinsupp 0 =
 (0 : ι ->₀ M)
参数：m != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem toFinsupp_zero [Zero M] [∀ m : M, Decidable (m ≠ 0)] : toFinsupp 0 = (0 : ι →₀ M) :=
  DFunLike.coe_injective rfl

@[simp]
/-
**DFinsupp.toFinsupp_add** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toFinsupp_add [AddZeroClass M] [forall m : M, Decidable (m != 0)] (f g : Π
₀ _ : ι, M) : (toFinsupp (f + g) : ι ->₀ M) = toFinsupp f + toFinsupp g
参数：m != 0；f g : Π₀ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `DFinsupp.coe_add`：coe_add [forall i, AddZeroClass (β i)] (g₁ g₂ : Π₀ i, 
β i) : ⇑(g₁ + g₂) = g₁ + g₂
-/
theorem toFinsupp_add [AddZeroClass M] [∀ m : M, Decidable (m ≠ 0)] (f g : Π₀ _ : ι, M) :
    (toFinsupp (f + g) : ι →₀ M) = toFinsupp f + toFinsupp g :=
  DFunLike.coe_injective <| DFinsupp.coe_add _ _

@[simp]
/-
**DFinsupp.toFinsupp_neg** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toFinsupp_neg [AddGroup M] [forall m : M, Decidable (m != 0)] (f : Π₀ _ : 
ι, M) : (toFinsupp (-f) : ι ->₀ M) = -toFinsupp f
参数：m != 0；f : Π₀ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `DFinsupp.coe_neg`：∀ {ι : Type u} {β : ι → Type v} [inst : (i : ι) → AddG
roup (β i)] (g : Π₀ (i : ι), β i), ⇑(-g) = -⇑g
-/
theorem toFinsupp_neg [AddGroup M] [∀ m : M, Decidable (m ≠ 0)] (f : Π₀ _ : ι, M) :
    (toFinsupp (-f) : ι →₀ M) = -toFinsupp f :=
  DFunLike.coe_injective <| DFinsupp.coe_neg _

@[simp]
/-
**DFinsupp.toFinsupp_sub** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toFinsupp_sub [AddGroup M] [forall m : M, Decidable (m != 0)] (f g : Π₀ _ 
: ι, M) : (toFinsupp (f - g) : ι ->₀ M) = toFinsupp f - toFinsupp g
参数：m != 0；f g : Π₀ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `DFinsupp.coe_sub`：coe_sub [forall i, AddGroup (β i)] (g₁ g₂ : Π₀ i, β i)
 : ⇑(g₁ - g₂) = g₁ - g₂
-/
theorem toFinsupp_sub [AddGroup M] [∀ m : M, Decidable (m ≠ 0)] (f g : Π₀ _ : ι, M) :
    (toFinsupp (f - g) : ι →₀ M) = toFinsupp f - toFinsupp g :=
  DFunLike.coe_injective <| DFinsupp.coe_sub _ _

@[simp]
/-
**DFinsupp.toFinsupp_smul** 是 Mathlib 中的一个定理，位于命名空间 `DFinsupp`。
形式化陈述：toFinsupp_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [forall m :
 M, Decidable (m != 0)] (r : R) (f : Π₀ _ : ι, M) : (toFinsupp (r • f) : ι ->₀ M
) = r • toFinsupp f
参数：m != 0；r : R；f : Π₀ _ : ι, M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `DFinsupp.coe_smul`：coe_smul [forall i, Zero (β i)] [forall i, SMulZeroCl
ass γ (β i)] (b : γ) (v : Π₀ i, β i) : ⇑(b • v) = b • ⇑v
-/
theorem toFinsupp_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [∀ m : M, Decidable (m ≠ 0)]
    (r : R) (f : Π₀ _ : ι, M) : (toFinsupp (r • f) : ι →₀ M) = r • toFinsupp f :=
  DFunLike.coe_injective <| DFinsupp.coe_smul _ _

end DFinsupp

end Lemmas

/-! ### Bundled `Equiv`s -/


section Equivs

/-- `Finsupp.toDFinsupp` and `DFinsupp.toFinsupp` together form an equiv. -/
@[simps -fullyApplied]
/-
**finsuppEquivDFinsupp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsuppEquivDFinsupp [DecidableEq ι] [Zero M] [forall m : M, Decidable (m 
!= 0)] : (ι ->₀ M) ≃ Π₀ _ : ι, M where toFun
参数：m != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_toFinsupp`：Finsupp.toDFinsupp_toFinsupp (f : ι ->₀ M)
 : f.toDFinsupp.toFinsupp = f
· 使用定理 `DFinsupp.toFinsupp_toDFinsupp`：DFinsupp.toFinsupp_toDFinsupp (f : Π₀ _ :
 ι, M) : f.toFinsupp.toDFinsupp = f

--- 原说明 ---
`Finsupp.toDFinsupp` and `DFinsupp.toFinsupp` together form an equiv.
-/
def finsuppEquivDFinsupp [DecidableEq ι] [Zero M] [∀ m : M, Decidable (m ≠ 0)] :
    (ι →₀ M) ≃ Π₀ _ : ι, M where
  toFun := Finsupp.toDFinsupp
  invFun := DFinsupp.toFinsupp
  left_inv := Finsupp.toDFinsupp_toFinsupp
  right_inv := DFinsupp.toFinsupp_toDFinsupp

/-- The additive version of `finsupp.toFinsupp`. Note that this is `noncomputable` because
`Finsupp.add` is noncomputable. -/
@[simps -fullyApplied]
/-
**finsuppAddEquivDFinsupp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsuppAddEquivDFinsupp [DecidableEq ι] [AddZeroClass M] [forall m : M, De
cidable (m != 0)] : (ι ->₀ M) ≃+ Π₀ _ : ι, M
参数：m != 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toDFinsupp_add`：toDFinsupp_add [AddZeroClass M] (f g : ι ->₀ M) 
: (f + g).toDFinsupp = f.toDFinsupp + g.toDFinsupp

--- 原说明 ---
The additive version of `finsupp.toFinsupp`. Note that this is `noncomputable` b
ecause
`Finsupp.add` is noncomputable.
-/
def finsuppAddEquivDFinsupp [DecidableEq ι] [AddZeroClass M] [∀ m : M, Decidable (m ≠ 0)] :
    (ι →₀ M) ≃+ Π₀ _ : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_add' := Finsupp.toDFinsupp_add }

variable (R)

/-- The additive version of `Finsupp.toFinsupp`. Note that this is `noncomputable` because
`Finsupp.add` is noncomputable. -/
/-
**finsuppLequivDFinsupp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finsuppLequivDFinsupp [DecidableEq ι] [Semiring R] [AddCommMonoid M] [fora
ll m : M, Decidable (m != 0)] [Module R M] : (ι ->₀ M) ≃ₗ[R] Π₀ _ : ι, M
参数：m != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive version of `Finsupp.toFinsupp`. Note that this is `noncomputable` b
ecause
`Finsupp.add` is noncomputable.
-/
def finsuppLequivDFinsupp [DecidableEq ι] [Semiring R] [AddCommMonoid M]
    [∀ m : M, Decidable (m ≠ 0)] [Module R M] : (ι →₀ M) ≃ₗ[R] Π₀ _ : ι, M :=
  { finsuppEquivDFinsupp with
    toFun := Finsupp.toDFinsupp
    invFun := DFinsupp.toFinsupp
    map_smul' := Finsupp.toDFinsupp_smul
    map_add' := Finsupp.toDFinsupp_add }

@[simp]
/-
**finsuppLequivDFinsupp_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppLequivDFinsupp_apply_apply [DecidableEq ι] [Semiring R] [AddCommMon
oid M] [forall m : M, Decidable (m != 0)] [Module R M] : (↑(finsuppLequivDFinsup
p (M
参数：m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finsuppLequivDFinsupp_apply_apply [DecidableEq ι] [Semiring R] [AddCommMonoid M]
    [∀ m : M, Decidable (m ≠ 0)] [Module R M] :
    (↑(finsuppLequivDFinsupp (M := M) R) : (ι →₀ M) → _) = Finsupp.toDFinsupp := rfl

@[simp]
/-
**finsuppLequivDFinsupp_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsuppLequivDFinsupp_symm_apply [DecidableEq ι] [Semiring R] [AddCommMono
id M] [forall m : M, Decidable (m != 0)] [Module R M] : ↑(LinearEquiv.symm (fins
uppLequivDFinsupp (ι
参数：m != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem finsuppLequivDFinsupp_symm_apply [DecidableEq ι] [Semiring R] [AddCommMonoid M]
    [∀ m : M, Decidable (m ≠ 0)] [Module R M] :
    ↑(LinearEquiv.symm (finsuppLequivDFinsupp (ι := ι) (M := M) R)) = DFinsupp.toFinsupp :=
  rfl

noncomputable section Sigma

/-! ### Stronger versions of `Finsupp.split` -/

variable {η : ι → Type*} {N : Type*} [Semiring R]

open Finsupp

set_option backward.isDefEq.respectTransparency false in
/-- `Finsupp.split` is an equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
/-
**sigmaFinsuppEquivDFinsupp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sigmaFinsuppEquivDFinsupp [Zero N] : ((Σ i, η i) ->₀ N) ≃ Π₀ i, η i ->₀ N 
where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.split` is an equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N
)`.
-/
def sigmaFinsuppEquivDFinsupp [Zero N] : ((Σ i, η i) →₀ N) ≃ Π₀ i, η i →₀ N where
  toFun f := ⟨split f, Trunc.mk ⟨(splitSupport f : Finset ι).val, fun i => by
          rw [← Finset.mem_def, mem_splitSupport_iff_nonzero]
          exact (em _).symm⟩⟩
  invFun f := by
    haveI := Classical.decEq ι
    haveI := fun i => Classical.decEq (η i →₀ N)
    refine
      onFinset (Finset.sigma f.support fun j => (f j).support) (fun ji => f ji.1 ji.2) fun g hg =>
        Finset.mem_sigma.mpr ⟨?_, mem_support_iff.mpr hg⟩
    simp only [Ne, DFinsupp.mem_support_toFun]
    intro h
    dsimp at hg
    rw [h] at hg
    simp only [coe_zero, Pi.zero_apply, not_true] at hg
  left_inv f := by ext; simp [split]
  right_inv f := by ext; simp [split]

@[simp]
/-
**sigmaFinsuppEquivDFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sigmaFinsuppEquivDFinsupp_apply [Zero N] (f : (Σ i, η i) ->₀ N) : (sigmaFi
nsuppEquivDFinsupp f : forall i, η i ->₀ N) = Finsupp.split f
参数：f : (Σ i, η i) ->₀ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigmaFinsuppEquivDFinsupp_apply [Zero N] (f : (Σ i, η i) →₀ N) :
    (sigmaFinsuppEquivDFinsupp f : ∀ i, η i →₀ N) = Finsupp.split f :=
  rfl

@[simp]
/-
**sigmaFinsuppEquivDFinsupp_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sigmaFinsuppEquivDFinsupp_symm_apply [Zero N] (f : Π₀ i, η i ->₀ N) (s : Σ
 i, η i) : (sigmaFinsuppEquivDFinsupp.symm f : (Σ i, η i) ->₀ N) s = f s.1 s.2
参数：f : Π₀ i, η i ->₀ N；s : Σ i, η i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem sigmaFinsuppEquivDFinsupp_symm_apply [Zero N] (f : Π₀ i, η i →₀ N) (s : Σ i, η i) :
    (sigmaFinsuppEquivDFinsupp.symm f : (Σ i, η i) →₀ N) s = f s.1 s.2 :=
  rfl

@[simp]
/-
**sigmaFinsuppEquivDFinsupp_support** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sigmaFinsuppEquivDFinsupp_support [DecidableEq ι] [Zero N] [forall (i : ι)
 (x : η i ->₀ N), Decidable (x != 0)] (f : (Σ i, η i) ->₀ N) : (sigmaFinsuppEqui
vDFinsupp f).support = Finsupp.splitSupport f
参数：i : ι；x : η i ->₀ N；x != 0；f : (Σ i, η i) ->₀ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.mem_support_toFun`：mem_support_toFun (f : Π₀ i, β i) (i) : i in
 f.support ↔ f i != 0
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Finsupp.mem_splitSupport_iff_nonzero`：mem_splitSupport_iff_nonzero (i : 
ι) : i in splitSupport l ↔ split l i != 0
-/
theorem sigmaFinsuppEquivDFinsupp_support [DecidableEq ι] [Zero N]
    [∀ (i : ι) (x : η i →₀ N), Decidable (x ≠ 0)] (f : (Σ i, η i) →₀ N) :
    (sigmaFinsuppEquivDFinsupp f).support = Finsupp.splitSupport f := by
  ext
  rw [DFinsupp.mem_support_toFun]
  exact (Finsupp.mem_splitSupport_iff_nonzero _ _).symm

@[simp]
/-
**sigmaFinsuppEquivDFinsupp_single** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sigmaFinsuppEquivDFinsupp_single [DecidableEq ι] [Zero N] (a : Σ i, η i) (
n : N) : sigmaFinsuppEquivDFinsupp (Finsupp.single a n) = @DFinsupp.single _ (fu
n i => η i ->₀ N) _ _ a.1 (Finsupp.single a.2 n)
参数：a : Σ i, η i；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.split_apply`：split_apply (i : ι) (x : αs i) : split l i x = l ⟨i
, x⟩
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem sigmaFinsuppEquivDFinsupp_single [DecidableEq ι] [Zero N] (a : Σ i, η i) (n : N) :
    sigmaFinsuppEquivDFinsupp (Finsupp.single a n) =
      @DFinsupp.single _ (fun i => η i →₀ N) _ _ a.1 (Finsupp.single a.2 n) := by
  obtain ⟨i, a⟩ := a
  ext j b
  by_cases h : i = j
  · subst h
    classical simp [split_apply, Finsupp.single_apply]
  suffices Finsupp.single (⟨i, a⟩ : Σ i, η i) n ⟨j, b⟩ = 0 by simp [split_apply, dif_neg h, this]
  have H : (⟨i, a⟩ : Σ i, η i) ≠ ⟨j, b⟩ := by simp [h]
  classical rw [Finsupp.single_apply, if_neg H]

-- Without this Lean fails to find the `AddZeroClass` instance on `Π₀ i, (η i →₀ N)`.
attribute [-instance] Finsupp.instZero

@[simp]
/-
**sigmaFinsuppEquivDFinsupp_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sigmaFinsuppEquivDFinsupp_add [AddZeroClass N] (f g : (Σ i, η i) ->₀ N) : 
sigmaFinsuppEquivDFinsupp (f + g) = (sigmaFinsuppEquivDFinsupp f + sigmaFinsuppE
quivDFinsupp g : Π₀ i : ι, η i ->₀ N)
参数：f g : (Σ i, η i) ->₀ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem sigmaFinsuppEquivDFinsupp_add [AddZeroClass N] (f g : (Σ i, η i) →₀ N) :
    sigmaFinsuppEquivDFinsupp (f + g) =
      (sigmaFinsuppEquivDFinsupp f + sigmaFinsuppEquivDFinsupp g : Π₀ i : ι, η i →₀ N) := by
  ext
  rfl

/-- `Finsupp.split` is an additive equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
@[simps]
/-
**sigmaFinsuppAddEquivDFinsupp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sigmaFinsuppAddEquivDFinsupp [AddZeroClass N] : ((Σ i, η i) ->₀ N) ≃+ Π₀ i
, η i ->₀ N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `sigmaFinsuppEquivDFinsupp_add`：sigmaFinsuppEquivDFinsupp_add [AddZeroCla
ss N] (f g : (Σ i, η i) ->₀ N) : sigmaFinsuppEquivDFinsupp (f + g) = (sigmaFinsu
ppEquivDFinsupp f +…

--- 原说明 ---
`Finsupp.split` is an additive equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, 
(η i →₀ N)`.
-/
def sigmaFinsuppAddEquivDFinsupp [AddZeroClass N] : ((Σ i, η i) →₀ N) ≃+ Π₀ i, η i →₀ N :=
  { sigmaFinsuppEquivDFinsupp with
    toFun := sigmaFinsuppEquivDFinsupp
    invFun := sigmaFinsuppEquivDFinsupp.symm
    map_add' := sigmaFinsuppEquivDFinsupp_add }

attribute [-instance] Finsupp.instAddZeroClass

@[simp]
/-
**sigmaFinsuppEquivDFinsupp_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sigmaFinsuppEquivDFinsupp_smul {R} [Monoid R] [AddMonoid N] [DistribMulAct
ion R N] (r : R) (f : (Σ i, η i) ->₀ N) : sigmaFinsuppEquivDFinsupp (r • f) = r 
• sigmaFinsuppEquivDFinsupp f
参数：r : R；f : (Σ i, η i) ->₀ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
-/
theorem sigmaFinsuppEquivDFinsupp_smul {R} [Monoid R] [AddMonoid N] [DistribMulAction R N] (r : R)
    (f : (Σ i, η i) →₀ N) :
    sigmaFinsuppEquivDFinsupp (r • f) = r • sigmaFinsuppEquivDFinsupp f := by
  ext
  rfl

attribute [-instance] Finsupp.instAddMonoid

/-- `Finsupp.split` is a linear equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
@[simps]
/-
**sigmaFinsuppLequivDFinsupp** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sigmaFinsuppLequivDFinsupp [AddCommMonoid N] [Module R N] : ((Σ i, η i) ->
₀ N) ≃ₗ[R] Π₀ i, η i ->₀ N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Finsupp.split` is a linear equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η 
i →₀ N)`.
-/
def sigmaFinsuppLequivDFinsupp [AddCommMonoid N] [Module R N] :
    ((Σ i, η i) →₀ N) ≃ₗ[R] Π₀ i, η i →₀ N :=
  { sigmaFinsuppAddEquivDFinsupp with
    map_smul' := sigmaFinsuppEquivDFinsupp_smul }

end Sigma

end Equivs

