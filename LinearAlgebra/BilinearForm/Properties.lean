/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Hom
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Bilinear form

This file defines various properties of bilinear forms, including reflexivity, symmetry,
alternativity, adjoint, and non-degeneracy.
For orthogonality, see `Mathlib/LinearAlgebra/BilinearForm/Orthogonal.lean`.

## Notation

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, i.e. `B x y = B.bilin x y`.

In this file we use the following type variables:
- `M`, `M'`, ... are modules over the commutative semiring `R`,
- `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
- `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

@[expose] public section


open LinearMap (BilinForm)
open Module

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {M' : Type*} [AddCommMonoid M'] [Module R M']
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/-! ### Reflexivity, symmetry, and alternativity -/


/-- The proposition that a bilinear form is reflexive -/
/-
**LinearMap.BilinForm.IsRefl** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：IsRefl (B : BilinForm R M) : Prop
参数：B : BilinForm R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a bilinear form is reflexive
-/
def IsRefl (B : BilinForm R M) : Prop := LinearMap.IsRefl B

namespace IsRefl

/-
**LinearMap.BilinForm.IsRefl.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinF
orm.IsRefl`。
形式化陈述：eq_zero (H : B.IsRefl) : forall {x y : M}, B x y = 0 -> B y x = 0
参数：H : B.IsRefl。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_zero (H : B.IsRefl) : ∀ {x y : M}, B x y = 0 → B y x = 0 := fun {x y} => H x y
/-
**LinearMap.BilinForm.IsRefl.neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm.
IsRefl`。
形式化陈述：∀ {R₁ : Type u_3} {M₁ : Type u_4} [inst : CommRing R₁] [inst_1 : AddCommGr
oup M₁] [inst_2 : _root_.Module R₁ M₁]   {B : LinearMap.BilinForm R₁ M₁}, B.IsRe
fl → (-B).IsRefl
参数：-B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsRefl) : (-B).IsRefl := fun x y =>
  neg_eq_zero.mpr ∘ hB x y ∘ neg_eq_zero.mp
/-
**LinearMap.BilinForm.IsRefl.smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm
.IsRefl`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {α : Type u_8} [inst_3 : Semiring α] [Is
Domain α] [inst_5 : _root_.Module α R] [inst_6 : SMulCommClass R α R]   [Module.
IsTorsionFree α R] (a : α) {B : LinearMap.BilinForm R M}, B.IsRefl → (a • B).IsR
efl
参数：a : α；a • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `smul_eq_zero_of_left`：smul_eq_zero_of_left (h : a = 0) (b : A) : a • b =
 0
· 使用引理 `smul_eq_zero_of_right`：smul_eq_zero_of_right (a : M) {b : A} (h : b = 0)
 : a • b = 0
-/
protected theorem smul {α : Type*} [Semiring α] [IsDomain α] [Module α R] [SMulCommClass R α R]
    [IsTorsionFree α R] (a : α) {B : BilinForm R M} (hB : B.IsRefl) :
    (a • B).IsRefl := fun _ _ h =>
  (smul_eq_zero.mp h).elim (fun ha => smul_eq_zero_of_left ha _) fun hBz =>
    smul_eq_zero_of_right _ (hB _ _ hBz)
/-
**LinearMap.BilinForm.IsRefl.groupSMul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bili
nForm.IsRefl`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {α : Type u_8} [inst_3 : Group α] [inst_
4 : DistribMulAction α R] [inst_5 : SMulCommClass R α R] (a : α)   {B : LinearMa
p.BilinForm R M}, B.IsRefl → (a • B).IsRefl
参数：a : α；a • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_eq_zero_iff_eq`：smul_eq_zero_iff_eq (a : α) {x : β} : a • x = 0 ↔ x
 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
protected theorem groupSMul {α} [Group α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsRefl) : (a • B).IsRefl := fun x y =>
  (smul_eq_zero_iff_eq _).mpr ∘ hB x y ∘ (smul_eq_zero_iff_eq _).mp

end IsRefl

@[simp]
/-
**LinearMap.BilinForm.isRefl_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm
`。
形式化陈述：isRefl_zero : (0 : BilinForm R M).IsRefl
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isRefl_zero : (0 : BilinForm R M).IsRefl := fun _ _ _ => rfl

@[simp]
/-
**LinearMap.BilinForm.isRefl_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：isRefl_neg {B : BilinForm R₁ M₁} : (-B).IsRefl ↔ B.IsRefl
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.IsRefl.neg`：∀ {R₁ : Type u_3} {M₁ : Type u_4} [inst 
: CommRing R₁] [inst_1 : AddCommGroup M₁] [inst_2 : _root_.Module R₁ M₁]   {B : 
LinearMap.BilinForm …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem isRefl_neg {B : BilinForm R₁ M₁} : (-B).IsRefl ↔ B.IsRefl :=
  ⟨fun h => neg_neg B ▸ h.neg, IsRefl.neg⟩

/-- The proposition that a bilinear form is symmetric -/
/-
**LinearMap.BilinForm.IsSymm** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommSemiring R] → [inst_1 
: AddCommMonoid M] → [inst_2 : _root_.Module R M] → LinearMap.BilinForm R M → Pr
op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a bilinear form is symmetric
-/
structure IsSymm (B : BilinForm R M) : Prop where
  protected eq : ∀ x y, B x y = B y x
/-
**LinearMap.BilinForm.isSymm_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：isSymm_def : IsSymm B ↔ forall x y, B x y = B y x where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSymm_def : IsSymm B ↔ ∀ x y, B x y = B y x where
  mp := fun ⟨h⟩ ↦ h
  mpr h := ⟨h⟩
/-
**LinearMap.BilinForm.isSymm_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：isSymm_iff : IsSymm B ↔ LinearMap.IsSymm B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSymm_iff : IsSymm B ↔ LinearMap.IsSymm B := by
  simp [isSymm_def, LinearMap.isSymm_def]

namespace IsSymm

/-
**LinearMap.BilinForm.IsSymm.isRefl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFo
rm.IsSymm`。
形式化陈述：isRefl (H : B.IsSymm) : B.IsRefl
参数：H : B.IsSymm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B : Li
nearMap.BilinForm R…
-/
theorem isRefl (H : B.IsSymm) : B.IsRefl := fun x y H1 => H.eq x y ▸ H1
/-
**LinearMap.BilinForm.IsSymm.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm.
IsSymm`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {B₁ B₂ : LinearMap.BilinForm R M}, B₁.Is
Symm → B₂.IsSymm → (B₁ + B₂).IsSymm
参数：B₁ + B₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `LinearMap.BilinForm.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B : Li
nearMap.BilinForm R…
-/
protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ + B₂).IsSymm := ⟨fun x y => (congr_arg₂ (· + ·) (hB₁.eq x y) (hB₂.eq x y) :)⟩
/-
**LinearMap.BilinForm.IsSymm.sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm.
IsSymm`。
形式化陈述：∀ {R₁ : Type u_3} {M₁ : Type u_4} [inst : CommRing R₁] [inst_1 : AddCommGr
oup M₁] [inst_2 : _root_.Module R₁ M₁]   {B₁ B₂ : LinearMap.BilinForm R₁ M₁}, B₁
.IsSymm → B₂.IsSymm → (B₁ - B₂).IsSymm
参数：B₁ - B₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `LinearMap.BilinForm.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B : Li
nearMap.BilinForm R…
-/
protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsSymm) (hB₂ : B₂.IsSymm) :
    (B₁ - B₂).IsSymm := ⟨fun x y => (congr_arg₂ Sub.sub (hB₁.eq x y) (hB₂.eq x y) :)⟩
/-
**LinearMap.BilinForm.IsSymm.neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm.
IsSymm`。
形式化陈述：∀ {R₁ : Type u_3} {M₁ : Type u_4} [inst : CommRing R₁] [inst_1 : AddCommGr
oup M₁] [inst_2 : _root_.Module R₁ M₁]   {B : LinearMap.BilinForm R₁ M₁}, B.IsSy
mm → (-B).IsSymm
参数：-B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B : Li
nearMap.BilinForm R…
-/
protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsSymm) : (-B).IsSymm := ⟨fun x y =>
  congr_arg Neg.neg (hB.eq x y)⟩
/-
**LinearMap.BilinForm.IsSymm.smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm
.IsSymm`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {α : Type u_8} [inst_3 : Monoid α] [inst
_4 : DistribMulAction α R] [inst_5 : SMulCommClass R α R] (a : α)   {B : LinearM
ap.BilinForm R M}, B.IsSymm → (a • B).IsSymm
参数：a : α；a • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B : Li
nearMap.BilinForm R…
-/
protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsSymm) : (a • B).IsSymm := ⟨fun x y =>
  congr_arg (a • ·) (hB.eq x y)⟩

/-- The restriction of a symmetric bilinear form on a submodule is also symmetric. -/
/-
**LinearMap.BilinForm.IsSymm.restrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bilin
Form.IsSymm`。
形式化陈述：restrict {B : BilinForm R M} (b : B.IsSymm) (W : Submodule R M) : (B.restr
ict W).IsSymm
参数：b : B.IsSymm；W : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B : Li
nearMap.BilinForm R…

--- 原说明 ---
The restriction of a symmetric bilinear form on a submodule is also symmetric.
-/
theorem restrict {B : BilinForm R M} (b : B.IsSymm) (W : Submodule R M) :
    (B.restrict W).IsSymm := ⟨fun x y => b.eq x y⟩

end IsSymm

@[simp]
/-
**LinearMap.BilinForm.isSymm_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm
`。
形式化陈述：isSymm_zero : (0 : BilinForm R M).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isSymm_zero : (0 : BilinForm R M).IsSymm := ⟨fun _ _ => rfl⟩

@[simp]
/-
**LinearMap.BilinForm.isSymm_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：isSymm_neg {B : BilinForm R₁ M₁} : (-B).IsSymm ↔ B.IsSymm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.IsSymm.neg`：∀ {R₁ : Type u_3} {M₁ : Type u_4} [inst 
: CommRing R₁] [inst_1 : AddCommGroup M₁] [inst_2 : _root_.Module R₁ M₁]   {B : 
LinearMap.BilinForm …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem isSymm_neg {B : BilinForm R₁ M₁} : (-B).IsSymm ↔ B.IsSymm :=
  ⟨fun h => neg_neg B ▸ h.neg, IsSymm.neg⟩
/-
**LinearMap.BilinForm.isSymm_iff_flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bilin
Form`。
形式化陈述：isSymm_iff_flip : B.IsSymm ↔ flipHom B = B where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.flip_apply`：flip_apply (A : BilinForm R M) (x y : M)
 : flipHom A x y = A y x
-/
theorem isSymm_iff_flip : B.IsSymm ↔ flipHom B = B where
  mp := fun ⟨h⟩ ↦ by ext; simp [h]
  mpr h := ⟨fun x y ↦ by rw [← flip_apply, h]⟩

section polarization

variable {R : Type*} [Field R] [NeZero (2 : R)] [Module R M] {B C : BilinForm R M}

/-- Polarization identity: a symmetric bilinear form can be expressed through the values
it takes on the diagonal. -/
/-
**LinearMap.BilinForm.IsSymm.polarization** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.B
ilinForm.IsSymm`。
形式化陈述：∀ {M : Type u_2} [inst : AddCommMonoid M] {R : Type u_8} [inst_1 : Field R
] [NeZero 2] [inst_3 : _root_.Module R M]   {B : LinearMap.BilinForm R M} (x y :
 M), B.IsSymm → (B x) y = ((B (x + y)) (x + y) - (B x) x - (B y) y) / 2
参数：x y : M；B x；(B (x + y)) (x + y) - (B x) x - (B y) y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LinearMap.BilinForm.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B : Li
nearMap.BilinForm R…
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf`：∀ {R : Type u_1} [inst : Comm
Semiring R] {a b c : R} (x : R) (e : ℕ), a + b = c → x ^ e * a + x ^ e * b = x ^
 e * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
Polarization identity: a symmetric bilinear form can be expressed through the va
lues
it takes on the diagonal.
-/
lemma IsSymm.polarization (x y : M) (hB : B.IsSymm) :
    B x y = (B (x + y) (x + y) - B x x - B y y) / 2 := by
  simp only [map_add, LinearMap.add_apply]
  rw [hB.eq y x]
  ring_nf
  rw [mul_assoc, inv_mul_cancel₀ two_ne_zero, mul_one]

/-- A symmetric bilinear form is characterized by the values it takes on the diagonal. -/
/-
**LinearMap.BilinForm.ext_of_isSymm** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.BilinFo
rm`。
形式化陈述：ext_of_isSymm (hB : IsSymm B) (hC : IsSymm C) (h : forall x, B x x = C x x
) : B = C
参数：hB : IsSymm B；hC : IsSymm C；h : forall x, B x x = C x x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.IsSymm.polarization`：∀ {M : Type u_2} [inst : AddCom
mMonoid M] {R : Type u_8} [inst_1 : Field R] [NeZero 2] [inst_3 : _root_.Module 
R M]   {B : LinearMap.BilinFo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A symmetric bilinear form is characterized by the values it takes on the diagona
l.
-/
lemma ext_of_isSymm (hB : IsSymm B) (hC : IsSymm C)
    (h : ∀ x, B x x = C x x) : B = C := by
  ext x y
  rw [hB.polarization, hC.polarization]
  simp_rw [h]

/-- A symmetric bilinear form is characterized by the values it takes on the diagonal. -/
/-
**LinearMap.BilinForm.ext_iff_of_isSymm** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bil
inForm`。
形式化陈述：ext_iff_of_isSymm (hB : IsSymm B) (hC : IsSymm C) : B = C ↔ forall x, B x 
x = C x x where mp h
参数：hB : IsSymm B；hC : IsSymm C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `LinearMap.BilinForm.ext_of_isSymm`：ext_of_isSymm (hB : IsSymm B) (hC : I
sSymm C) (h : forall x, B x x = C x x) : B = C

--- 原说明 ---
A symmetric bilinear form is characterized by the values it takes on the diagona
l.
-/
lemma ext_iff_of_isSymm (hB : IsSymm B) (hC : IsSymm C) :
    B = C ↔ ∀ x, B x x = C x x where
  mp h := by simp [h]
  mpr := ext_of_isSymm hB hC

end polarization

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.BilinForm.isSymm_iff_basis** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bili
nForm`。
形式化陈述：isSymm_iff_basis {ι : Type*} (b : Basis ι R M) : IsSymm B ↔ forall i j, B 
(b i) (b j) = B (b j) (b i) where mp
参数：b : Basis ι R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Submodule.mem_span_iff_exists_finset_subset`：Submodule.mem_span_iff_exis
ts_finset_subset {s : Set M} {x : M} : x in span R s ↔ exists (f : M -> R) (t : 
Finset M), ↑t subseteq s ∧ f.supp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
-/
lemma isSymm_iff_basis {ι : Type*} (b : Basis ι R M) :
    IsSymm B ↔ ∀ i j, B (b i) (b j) = B (b j) (b i) where
  mp := fun ⟨h⟩ i j ↦ h _ _
  mpr := by
    refine fun h ↦ ⟨fun x y ↦ ?_⟩
    obtain ⟨fx, tx, ix, -, hx⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : x ∈ Submodule.span R (Set.range b))
    obtain ⟨fy, ty, iy, -, hy⟩ := Submodule.mem_span_iff_exists_finset_subset.1
      (by simp : y ∈ Submodule.span R (Set.range b))
    rw [← hx, ← hy]
    simp only [map_sum, map_smul, coe_sum, Finset.sum_apply, smul_apply, smul_eq_mul,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b₁ h₁ ↦ Finset.sum_congr rfl fun b₂ h₂ ↦ ?_)
    rw [mul_left_comm]
    obtain ⟨i, rfl⟩ := ix h₁
    obtain ⟨j, rfl⟩ := iy h₂
    rw [h]

/-! ### Positive semidefinite bilinear forms -/

section PositiveSemidefinite

/-- A bilinear form `B` is **nonnegative** if for any `x` we have `0 ≤ B x x`. -/
/-
**LinearMap.BilinForm.IsNonneg** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommSemiring R] →       [i
nst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → [LE R] → LinearMap.Bil
inForm R M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bilinear form `B` is **nonnegative** if for any `x` we have `0 ≤ B x x`.
-/
structure IsNonneg [LE R] (B : BilinForm R M) where
  nonneg : ∀ x, 0 ≤ B x x
/-
**LinearMap.BilinForm.isNonneg_def** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.BilinFor
m`。
形式化陈述：isNonneg_def [LE R] {B : BilinForm R M} : B.IsNonneg ↔ forall x, 0 <= B x 
x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isNonneg_def [LE R] {B : BilinForm R M} : B.IsNonneg ↔ ∀ x, 0 ≤ B x x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

/-- A bilinear form is nonnegative if and only if it is nonnegative as a sesquilinear form. -/
/-
**LinearMap.BilinForm.isNonneg_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.BilinFor
m`。
形式化陈述：isNonneg_iff [LE R] {B : BilinForm R M} : B.IsNonneg ↔ LinearMap.IsNonneg 
B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `LinearMap.BilinForm.isNonneg_def`：isNonneg_def [LE R] {B : BilinForm R M
} : B.IsNonneg ↔ forall x, 0 <= B x x
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LinearMap.isNonneg_def`：isNonneg_def [LE R] {B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R
} : B.IsNonneg ↔ forall x, 0 <= B x x

--- 原说明 ---
A bilinear form is nonnegative if and only if it is nonnegative as a sesquilinea
r form.
-/
lemma isNonneg_iff [LE R] {B : BilinForm R M} : B.IsNonneg ↔ LinearMap.IsNonneg B :=
  isNonneg_def.trans LinearMap.isNonneg_def.symm

@[simp]
/-
**LinearMap.BilinForm.isNonneg_zero** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.BilinFo
rm`。
形式化陈述：isNonneg_zero [Preorder R] : IsNonneg (0 : BilinForm R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.BilinForm.isNonneg_iff`：isNonneg_iff [LE R] {B : BilinForm R M
} : B.IsNonneg ↔ LinearMap.IsNonneg B
· 使用引理 `LinearMap.isNonneg_zero`：isNonneg_zero [Preorder R] : IsNonneg (0 : M ->
ₛₗ[I₁] M ->ₛₗ[I₂] R)
-/
lemma isNonneg_zero [Preorder R] : IsNonneg (0 : BilinForm R M) :=
  isNonneg_iff.2 LinearMap.isNonneg_zero
/-
**LinearMap.BilinForm.IsNonneg.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFor
m.IsNonneg`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [inst_3 : Preorder R] [AddLeftMono R] {B
 C : LinearMap.BilinForm R M}, B.IsNonneg → C.IsNonneg → (B + C).IsNonneg
参数：B + C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `LinearMap.BilinForm.IsNonneg.nonneg`：∀ {R : Type u_1} {M : Type u_2} [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
inst_3 : LE R] {B : Linea…
-/
protected lemma IsNonneg.add [Preorder R] [AddLeftMono R] {B C : BilinForm R M}
    (hB : B.IsNonneg) (hC : C.IsNonneg) : (B + C).IsNonneg where
  nonneg x := add_nonneg (hB.nonneg x) (hC.nonneg x)
/-
**LinearMap.BilinForm.IsNonneg.smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFo
rm.IsNonneg`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [inst_3 : Preorder R] [PosMulMono R] {B 
: LinearMap.BilinForm R M} {c : R}, B.IsNonneg → 0 ≤ c → (c • B).IsNonneg
参数：c • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `LinearMap.BilinForm.IsNonneg.nonneg`：∀ {R : Type u_1} {M : Type u_2} [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
inst_3 : LE R] {B : Linea…
-/
protected lemma IsNonneg.smul [Preorder R] [PosMulMono R] {B : BilinForm R M} {c : R}
    (hB : B.IsNonneg) (hc : 0 ≤ c) : (c • B).IsNonneg where
  nonneg x := mul_nonneg hc (hB.nonneg x)

/-- A bilinear form `B` is **positive semidefinite** if it is symmetric and nonnegative. -/
/-
**LinearMap.BilinForm.IsPosSemidef** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap.BilinF
orm`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommSemiring R] →       [i
nst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → [LE R] → LinearMap.Bil
inForm R M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bilinear form `B` is **positive semidefinite** if it is symmetric and nonnegat
ive.
-/
structure IsPosSemidef [LE R] (B : BilinForm R M) extends
  isSymm : B.IsSymm,
  isNonneg : B.IsNonneg

variable {B : BilinForm R M}
/-
**LinearMap.BilinForm.isPosSemidef_def** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bili
nForm`。
形式化陈述：isPosSemidef_def [LE R] : B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.IsPosSemidef.isSymm`：∀ {R : Type u_1} {M : Type u_2}
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]
   [inst_3 : LE R] {B : Linea…
· 使用定理 `LinearMap.BilinForm.IsPosSemidef.isNonneg`：∀ {R : Type u_1} {M : Type u_
2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R 
M]   [inst_3 : LE R] {B : Linea…
-/
lemma isPosSemidef_def [LE R] : B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg :=
  ⟨fun h ↦ ⟨h.isSymm, h.isNonneg⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

/-- A bilinear form is positive semidefinite if and only if it is positive semidefinite
  as a sesquilinear form. -/
/-
**LinearMap.BilinForm.isPosSemidef_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bili
nForm`。
形式化陈述：isPosSemidef_iff [LE R] {B : BilinForm R M} : B.IsPosSemidef ↔ LinearMap.I
sPosSemidef B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `LinearMap.BilinForm.isPosSemidef_def`：isPosSemidef_def [LE R] : B.IsPosS
emidef ↔ B.IsSymm ∧ B.IsNonneg
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `LinearMap.BilinForm.isSymm_iff`：isSymm_iff : IsSymm B ↔ LinearMap.IsSymm
 B
· 使用引理 `LinearMap.BilinForm.isNonneg_iff`：isNonneg_iff [LE R] {B : BilinForm R M
} : B.IsNonneg ↔ LinearMap.IsNonneg B
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `LinearMap.isPosSemidef_def`：isPosSemidef_def [LE R] {B : M ->ₛₗ[I₁] M ->
ₗ[R] R} : B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg

--- 原说明 ---
A bilinear form is positive semidefinite if and only if it is positive semidefin
ite
  as a sesquilinear form.
-/
lemma isPosSemidef_iff [LE R] {B : BilinForm R M} : B.IsPosSemidef ↔ LinearMap.IsPosSemidef B :=
  isPosSemidef_def.trans <| (isSymm_iff.and isNonneg_iff).trans LinearMap.isPosSemidef_def.symm

@[simp]
/-
**LinearMap.BilinForm.isPosSemidef_zero** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bil
inForm`。
形式化陈述：isPosSemidef_zero [Preorder R] : IsPosSemidef (0 : BilinForm R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.BilinForm.isPosSemidef_iff`：isPosSemidef_iff [LE R] {B : Bilin
Form R M} : B.IsPosSemidef ↔ LinearMap.IsPosSemidef B
· 使用引理 `LinearMap.isPosSemidef_zero`：isPosSemidef_zero [Preorder R] : IsPosSemid
ef (0 : M ->ₛₗ[I₁] M ->ₗ[R] R) where isSymm
-/
lemma isPosSemidef_zero [Preorder R] : IsPosSemidef (0 : BilinForm R M) :=
  isPosSemidef_iff.2 LinearMap.isPosSemidef_zero
/-
**LinearMap.BilinForm.IsPosSemidef.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bili
nForm.IsPosSemidef`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [inst_3 : Preorder R] [AddLeftMono R] {B
 C : LinearMap.BilinForm R M},   B.IsPosSemidef → C.IsPosSemidef → (B + C).IsPos
Semidef
参数：B + C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.BilinForm.isPosSemidef_iff`：isPosSemidef_iff [LE R] {B : Bilin
Form R M} : B.IsPosSemidef ↔ LinearMap.IsPosSemidef B
· 使用定理 `LinearMap.IsPosSemidef.add`：∀ {R : Type u_1} {M : Type u_5} [inst : Comm
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I₁ : R →+
* R} [inst_3 : P…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
protected lemma IsPosSemidef.add [Preorder R] [AddLeftMono R] {B C : BilinForm R M}
    (hB : B.IsPosSemidef) (hC : C.IsPosSemidef) : (B + C).IsPosSemidef :=
  isPosSemidef_iff.2 ((isPosSemidef_iff.1 hB).add (isPosSemidef_iff.1 hC))
/-
**LinearMap.BilinForm.IsPosSemidef.smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inForm.IsPosSemidef`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [inst_3 : Preorder R] [PosMulMono R] {B 
: LinearMap.BilinForm R M} {c : R},   B.IsPosSemidef → 0 ≤ c → (c • B).IsPosSemi
def
参数：c • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `LinearMap.BilinForm.isPosSemidef_def`：isPosSemidef_def [LE R] : B.IsPosS
emidef ↔ B.IsSymm ∧ B.IsNonneg
· 使用定理 `LinearMap.BilinForm.IsSymm.smul`：∀ {R : Type u_1} {M : Type u_2} [inst :
 CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {α : 
Type u_8} [inst_3 : M…
· 使用定理 `LinearMap.BilinForm.IsPosSemidef.isSymm`：∀ {R : Type u_1} {M : Type u_2}
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]
   [inst_3 : LE R] {B : Linea…
· 使用定理 `LinearMap.BilinForm.IsNonneg.smul`：∀ {R : Type u_1} {M : Type u_2} [inst
 : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [in
st_3 : Preorder R] [Pos…
· 使用定理 `LinearMap.BilinForm.IsPosSemidef.isNonneg`：∀ {R : Type u_1} {M : Type u_
2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R 
M]   [inst_3 : LE R] {B : Linea…
-/
protected lemma IsPosSemidef.smul [Preorder R] [PosMulMono R] {B : BilinForm R M} {c : R}
    (hB : B.IsPosSemidef) (hc : 0 ≤ c) : (c • B).IsPosSemidef :=
  isPosSemidef_def.2 ⟨hB.isSymm.smul c, hB.isNonneg.smul hc⟩

end PositiveSemidefinite

/-- The proposition that a bilinear form is alternating -/
/-
**LinearMap.BilinForm.IsAlt** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：IsAlt (B : BilinForm R M) : Prop
参数：B : BilinForm R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a bilinear form is alternating
-/
def IsAlt (B : BilinForm R M) : Prop := LinearMap.IsAlt B

namespace IsAlt

/-
**LinearMap.BilinForm.IsAlt.self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm.IsAlt`。
形式化陈述：self_eq_zero (H : B.IsAlt) (x : M) : B x x = 0
参数：H : B.IsAlt；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsAlt.self_eq_zero`：∀ {R : Type u_1} {R₁ : Type u_2} {M : Type
 u_5} {M₁ : Type u_6} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst
_2 : _root_.Module…
-/
theorem self_eq_zero (H : B.IsAlt) (x : M) : B x x = 0 := LinearMap.IsAlt.self_eq_zero H x
/-
**LinearMap.BilinForm.IsAlt.neg_eq** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFor
m.IsAlt`。
形式化陈述：neg_eq (H : B₁.IsAlt) (x y : M₁) : -B₁ x y = B₁ y x
参数：H : B₁.IsAlt；x y : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsAlt.neg`：neg (H : B.IsAlt) (x y : M₁) : -B x y = B y x
-/
theorem neg_eq (H : B₁.IsAlt) (x y : M₁) : -B₁ x y = B₁ y x := LinearMap.IsAlt.neg H x y
/-
**LinearMap.BilinForm.IsAlt.isRefl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFor
m.IsAlt`。
形式化陈述：isRefl (H : B₁.IsAlt) : B₁.IsRefl
参数：H : B₁.IsAlt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsAlt.isRefl`：isRefl (H : B.IsAlt) : B.IsRefl
-/
theorem isRefl (H : B₁.IsAlt) : B₁.IsRefl := LinearMap.IsAlt.isRefl H
/-
**LinearMap.BilinForm.IsAlt.eq_of_add_add_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.BilinForm.IsAlt`。
形式化陈述：eq_of_add_add_eq_zero [IsCancelAdd R] {a b c : M} (H : B.IsAlt) (hAdd : a 
+ b + c = 0) : B a b = B b c
参数：H : B.IsAlt；hAdd : a + b + c = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsAlt.eq_of_add_add_eq_zero`：∀ {R : Type u_1} {R₁ : Type u_2} 
{M : Type u_5} {M₁ : Type u_6} [inst : CommSemiring R] [inst_1 : AddCommMonoid M
]   [inst_2 : _root_.Module…
-/
theorem eq_of_add_add_eq_zero [IsCancelAdd R] {a b c : M} (H : B.IsAlt) (hAdd : a + b + c = 0) :
    B a b = B b c := LinearMap.IsAlt.eq_of_add_add_eq_zero H hAdd
/-
**LinearMap.BilinForm.IsAlt.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm.I
sAlt`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {B₁ B₂ : LinearMap.BilinForm R M}, B₁.Is
Alt → B₂.IsAlt → (B₁ + B₂).IsAlt
参数：B₁ + B₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
protected theorem add {B₁ B₂ : BilinForm R M} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) : (B₁ + B₂).IsAlt :=
  fun x => (congr_arg₂ (· + ·) (hB₁ x) (hB₂ x) :).trans <| add_zero _
/-
**LinearMap.BilinForm.IsAlt.sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm.I
sAlt`。
形式化陈述：∀ {R₁ : Type u_3} {M₁ : Type u_4} [inst : CommRing R₁] [inst_1 : AddCommGr
oup M₁] [inst_2 : _root_.Module R₁ M₁]   {B₁ B₂ : LinearMap.BilinForm R₁ M₁}, B₁
.IsAlt → B₂.IsAlt → (B₁ - B₂).IsAlt
参数：B₁ - B₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
protected theorem sub {B₁ B₂ : BilinForm R₁ M₁} (hB₁ : B₁.IsAlt) (hB₂ : B₂.IsAlt) :
    (B₁ - B₂).IsAlt := fun x => (congr_arg₂ Sub.sub (hB₁ x) (hB₂ x)).trans <| sub_zero _
/-
**LinearMap.BilinForm.IsAlt.neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm.I
sAlt`。
形式化陈述：∀ {R₁ : Type u_3} {M₁ : Type u_4} [inst : CommRing R₁] [inst_1 : AddCommGr
oup M₁] [inst_2 : _root_.Module R₁ M₁]   {B : LinearMap.BilinForm R₁ M₁}, B.IsAl
t → (-B).IsAlt
参数：-B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
-/
protected theorem neg {B : BilinForm R₁ M₁} (hB : B.IsAlt) : (-B).IsAlt := fun x =>
  neg_eq_zero.mpr <| hB x
/-
**LinearMap.BilinForm.IsAlt.smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm.
IsAlt`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {α : Type u_8} [inst_3 : Monoid α] [inst
_4 : DistribMulAction α R] [inst_5 : SMulCommClass R α R] (a : α)   {B : LinearM
ap.BilinForm R M}, B.IsAlt → (a • B).IsAlt
参数：a : α；a • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
protected theorem smul {α} [Monoid α] [DistribMulAction α R] [SMulCommClass R α R] (a : α)
    {B : BilinForm R M} (hB : B.IsAlt) : (a • B).IsAlt := fun x =>
  (congr_arg (a • ·) (hB x)).trans <| smul_zero _

end IsAlt

@[simp]
/-
**LinearMap.BilinForm.isAlt_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：isAlt_zero : (0 : BilinForm R M).IsAlt
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isAlt_zero : (0 : BilinForm R M).IsAlt := fun _ => rfl

@[simp]
/-
**LinearMap.BilinForm.isAlt_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：isAlt_neg {B : BilinForm R₁ M₁} : (-B).IsAlt ↔ B.IsAlt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.IsAlt.neg`：∀ {R₁ : Type u_3} {M₁ : Type u_4} [inst :
 CommRing R₁] [inst_1 : AddCommGroup M₁] [inst_2 : _root_.Module R₁ M₁]   {B : L
inearMap.BilinForm …
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
theorem isAlt_neg {B : BilinForm R₁ M₁} : (-B).IsAlt ↔ B.IsAlt :=
  ⟨fun h => neg_neg B ▸ h.neg, IsAlt.neg⟩

end BilinForm

namespace BilinForm


-- Note: This originally involved only left-separating, and was changed (January 2026, PR #34110)
-- to be symmetric to match `LinearMap.Nondegenerate`. See discussion at this Zulip thread:
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/Nondegenerate.20bilinear.20.2F.20quadratic.20forms/with/568863325
-- TODO: Should it be removed entirely?
/--
A nondegenerate bilinear form is a bilinear form that is both left-separating and
right-separating, i.e. if `B x y = 0` for all `y` then `x = 0`, and if `B x y = 0` for all `x` then
`y = 0`.

Note that these conditions are independent of each other in general, but in the common case of
finite-dimensional vector spaces (or, more generally, finite free modules over an integral
domain), either of these conditions implies the other; see
`LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft` and
`LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot`, proved in a later file.
-/
/-
**LinearMap.BilinForm.Nondegenerate** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearMap.Bilin
Form`。
形式化陈述：Nondegenerate (B : BilinForm R M) : Prop
参数：B : BilinForm R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nondegenerate bilinear form is a bilinear form that is both left-separating an
d
right-separating, i.e. if `B x y = 0` for all `y` then `x = 0`, and if `B x y = 
0` for all `x` then
`y = 0`.

Note that these conditions are independent of each other in general, but in the 
common case of
finite-dimensional vector spaces (or, more generally, finite free modules over a
n integral
domain), either of these conditions implies the other; see
`LinearMap.BilinForm.Nondegenerate.ofSeparatingLeft` and
`LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot`, proved in a later file.
-/
abbrev Nondegenerate (B : BilinForm R M) : Prop :=
  LinearMap.Nondegenerate B

section

variable (R M)

/-- In a non-trivial module, zero is not non-degenerate. -/
/-
**LinearMap.BilinForm.not_nondegenerate_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p.BilinForm`。
形式化陈述：not_nondegenerate_zero [Nontrivial M] : ¬(0 : BilinForm R M).Nondegenerate
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
In a non-trivial module, zero is not non-degenerate.
-/
theorem not_nondegenerate_zero [Nontrivial M] : ¬(0 : BilinForm R M).Nondegenerate :=
  let ⟨m, hm⟩ := exists_ne (0 : M)
  fun h => hm (h.1 m fun _ => rfl)

end

variable {M' : Type*}
variable [AddCommMonoid M'] [Module R M']

/-
**LinearMap.BilinForm.Nondegenerate.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
.BilinForm.Nondegenerate`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   [Nontrivial M] {B : LinearMap.BilinForm 
R M}, B.Nondegenerate → B ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.not_nondegenerate_zero`：not_nondegenerate_zero [Nont
rivial M] : ¬(0 : BilinForm R M).Nondegenerate
-/
theorem Nondegenerate.ne_zero [Nontrivial M] {B : BilinForm R M} (h : B.Nondegenerate) : B ≠ 0 :=
  fun h0 => not_nondegenerate_zero R M <| h0 ▸ h
/-
**LinearMap.BilinForm.Nondegenerate.congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.B
ilinForm.Nondegenerate`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {M' : Type u_8} [inst_3 : AddCommMonoid 
M'] [inst_4 : _root_.Module R M'] {B : LinearMap.BilinForm R M}   (e : M ≃ₗ[R] M
'), B.Nondegenerate → ((LinearMap.BilinForm.congr e) B).Nondegenerate
参数：e : M ≃ₗ[R] M'；(LinearMap.BilinForm.congr e) B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.SeparatingLeft.congr`：∀ {R : Type u_1} {M : Type u_5} {Mₗ₁ : T
ype u_9} {Mₗ₁' : Type u_10} {Mₗ₂ : Type u_11} {Mₗ₂' : Type u_12}   [inst : CommS
emiring R] [inst_1 :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Nondegenerate.congr {B : BilinForm R M} (e : M ≃ₗ[R] M') (h : B.Nondegenerate) :
    (congr e B).Nondegenerate :=
  ⟨h.1.congr e e, show (BilinForm.congr e (flip B)).SeparatingLeft from .congr e e h.2⟩

@[simp]
/-
**LinearMap.BilinForm.nondegenerate_congr_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.BilinForm`。
形式化陈述：nondegenerate_congr_iff {B : BilinForm R M} (e : M ≃ₗ[R] M') : (congr e B)
.Nondegenerate ↔ B.Nondegenerate
参数：e : M ≃ₗ[R] M'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.congr_congr`：congr_congr (e : M' ≃ₗ[R] M'') (f : M ≃
ₗ[R] M') (B : BilinForm R M) : congr e (congr f B) = congr (f.trans e) B
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用定理 `LinearMap.BilinForm.congr_refl`：congr_refl : congr (LinearEquiv.refl R M
) = LinearEquiv.refl R _
· 使用定理 `LinearEquiv.refl_apply`：refl_apply [Module R M] (x : M) : refl R M x = x
· 使用定理 `LinearMap.BilinForm.Nondegenerate.congr`：∀ {R : Type u_1} {M : Type u_2}
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]
   {M' : Type u_8} [inst_3 : …
-/
theorem nondegenerate_congr_iff {B : BilinForm R M} (e : M ≃ₗ[R] M') :
    (congr e B).Nondegenerate ↔ B.Nondegenerate :=
  ⟨fun h => by
    convert! h.congr e.symm
    rw [congr_congr, e.self_trans_symm, congr_refl, LinearEquiv.refl_apply], Nondegenerate.congr e⟩
/-
**LinearMap.BilinForm.Nondegenerate.ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.BilinForm.Nondegenerate`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {B : LinearMap.BilinForm R M}, B.Nondege
nerate → LinearMap.ker B = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Nondegenerate.ker_eq_bot {B : BilinForm R M} (h : B.Nondegenerate) :
    LinearMap.ker B = ⊥ := LinearMap.separatingLeft_iff_ker_eq_bot.mp h.1
/-
**LinearMap.BilinForm.compLeft_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：compLeft_injective (B : BilinForm R₁ M₁) (b : B.Nondegenerate) : Function.
Injective B.compLeft
参数：B : BilinForm R₁ M₁；b : B.Nondegenerate。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.sub_left`：sub_left (x y z : M₁) : B₁ (x - y) z = B₁ 
x z - B₁ y z
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.compLeft_apply`：compLeft_apply (B : BilinForm R M) (
f : M ->ₗ[R] M) (v w) : B.compLeft f v w = B (f v) w
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem compLeft_injective (B : BilinForm R₁ M₁) (b : B.Nondegenerate) :
    Function.Injective B.compLeft := fun φ ψ h => by
  ext w
  refine eq_of_sub_eq_zero (b.1 _ ?_)
  intro v
  rw [sub_left, ← compLeft_apply, ← compLeft_apply, ← h, sub_self]
/-
**LinearMap.BilinForm.isAdjointPair_unique_of_nondegenerate** 是 Mathlib 中的一个定理，位
于命名空间 `LinearMap.BilinForm`。
形式化陈述：isAdjointPair_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondege
nerate) (φ ψ₁ ψ₂ : M₁ ->ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjoin
tPair B B ψ₂ φ) : ψ₁ = ψ₂
参数：B : BilinForm R₁ M₁；b : B.Nondegenerate；φ ψ₁ ψ₂ : M₁ ->ₗ[R₁] M₁；hψ₁ : IsAdjoi
ntPair B B ψ₁ φ；hψ₂ : IsAdjointPair B B ψ₂ φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.compLeft_injective`：compLeft_injective (B : BilinFor
m R₁ M₁) (b : B.Nondegenerate) : Function.Injective B.compLeft
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.compLeft_apply`：compLeft_apply (B : BilinForm R M) (
f : M ->ₗ[R] M) (v w) : B.compLeft f v w = B (f v) w
-/
theorem isAdjointPair_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondegenerate)
    (φ ψ₁ ψ₂ : M₁ →ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (hψ₂ : IsAdjointPair B B ψ₂ φ) :
    ψ₁ = ψ₂ :=
  B.compLeft_injective b <| ext fun v w => by rw [compLeft_apply, compLeft_apply, hψ₁, hψ₂]
/-
**LinearMap.BilinForm.Nondegenerate.flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm.Nondegenerate`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {B : LinearMap.BilinForm R M}, B.Nondege
nerate → B.flip.Nondegenerate
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma Nondegenerate.flip {B : BilinForm R M} (hB : B.Nondegenerate) :
    B.flip.Nondegenerate :=
  ⟨hB.2, hB.1⟩
/-
**LinearMap.BilinForm.nondegenerate_flip_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMa
p.BilinForm`。
形式化陈述：nondegenerate_flip_iff {B : BilinForm R M} : B.flip.Nondegenerate ↔ B.Nond
egenerate
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.Nondegenerate.flip`：∀ {R : Type u_1} {M : Type u_2} 
[inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] 
  {B : LinearMap.BilinForm R…
-/
lemma nondegenerate_flip_iff {B : BilinForm R M} :
    B.flip.Nondegenerate ↔ B.Nondegenerate := ⟨Nondegenerate.flip, Nondegenerate.flip⟩

section FiniteDimensional

variable [FiniteDimensional K V]

/-- Given a nondegenerate bilinear form `B` on a finite-dimensional vector space, `B.toDual` is
the linear equivalence between a vector space and its dual. -/
/-
**LinearMap.BilinForm.toDual** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：toDual (B : BilinForm K V) (b : B.Nondegenerate) : V ≃ₗ[K] Module.Dual K V
参数：B : BilinForm K V；b : B.Nondegenerate。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a nondegenerate bilinear form `B` on a finite-dimensional vector space, `B
.toDual` is
the linear equivalence between a vector space and its dual.
-/
noncomputable def toDual (B : BilinForm K V) (b : B.Nondegenerate) : V ≃ₗ[K] Module.Dual K V :=
  B.linearEquivOfInjective (LinearMap.ker_eq_bot.mp <| b.ker_eq_bot)
    Subspace.dual_finrank_eq.symm
/-
**LinearMap.BilinForm.toDual_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：toDual_def {B : BilinForm K V} (b : B.Nondegenerate) {m n : V} : B.toDual 
b m n = B m n
参数：b : B.Nondegenerate。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toDual_def {B : BilinForm K V} (b : B.Nondegenerate) {m n : V} : B.toDual b m n = B m n :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.apply_toDual_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `LinearM
ap.BilinForm`。
形式化陈述：apply_toDual_symm_apply {B : BilinForm K V} {hB : B.Nondegenerate} (f : Mo
dule.Dual K V) (v : V) : B ((B.toDual hB).symm f) v = f v
参数：f : Module.Dual K V；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma apply_toDual_symm_apply {B : BilinForm K V} {hB : B.Nondegenerate}
    (f : Module.Dual K V) (v : V) :
    B ((B.toDual hB).symm f) v = f v := by
  change B.toDual hB ((B.toDual hB).symm f) v = f v
  simp only [LinearEquiv.apply_symm_apply]

@[deprecated (since := "2026-01-17")] alias nonDegenerateFlip_iff := nondegenerate_flip_iff

end FiniteDimensional

section DualBasis

variable {ι : Type*} [DecidableEq ι] [Finite ι]

/-- The `B`-dual basis `B.dualBasis hB b` to a finite basis `b` satisfies
`B (B.dualBasis hB b i) (b j) = B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0`,
where `B` is a nondegenerate (symmetric) bilinear form and `b` is a finite basis. -/
/-
**LinearMap.BilinForm.dualBasis** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) : B
asis ι K V
参数：B : BilinForm K V；hB : B.Nondegenerate；b : Basis ι K V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `B`-dual basis `B.dualBasis hB b` to a finite basis `b` satisfies
`B (B.dualBasis hB b i) (b j) = B (b i) (B.dualBasis hB b j) = if i = j then 1 e
lse 0`,
where `B` is a nondegenerate (symmetric) bilinear form and `b` is a finite basis
.
-/
noncomputable def dualBasis (B : BilinForm K V) (hB : B.Nondegenerate) (b : Basis ι K V) :
    Basis ι K V :=
  haveI := b.finiteDimensional_of_finite
  b.dualBasis.map (B.toDual hB).symm

variable {B : BilinForm K V}

@[simp]
/-
**LinearMap.BilinForm.dualBasis_repr_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.
BilinForm`。
形式化陈述：dualBasis_repr_apply (hB : B.Nondegenerate) (b : Basis ι K V) (x i) : (B.d
ualBasis hB b).repr x i = B x (b i)
参数：hB : B.Nondegenerate；b : Basis ι K V；x i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.dualBasis.eq_1`：∀ {V : Type u_5} {K : Type u_6} [ins
t : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι : Type u_
9}   [inst_3 : Decidable…
· 使用定理 `Module.Basis.map_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} {M
' : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.
Module R M]…
· 使用定理 `LinearEquiv.symm_symm`：symm_symm (e : M ≃ₛₗ[σ] M₂) : e.symm.symm = e
· 使用定理 `LinearEquiv.trans_apply`：trans_apply (c : M₁) : (e₁₂.trans e₂₃ : M₁ ≃ₛₗ[
σ₁₃] M₃) c = e₂₃ (e₁₂ c)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Basis.dualBasis_repr`：∀ {R : Type uR} {M : Type uM} {ι : Type uι}
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R 
M] [inst_3 : Deci…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.BilinForm.toDual_def`：toDual_def {B : BilinForm K V} (b : B.No
ndegenerate) {m n : V} : B.toDual b m n = B m n
-/
theorem dualBasis_repr_apply (hB : B.Nondegenerate) (b : Basis ι K V) (x i) :
    (B.dualBasis hB b).repr x i = B x (b i) := by
  have := b.finiteDimensional_of_finite
  rw [dualBasis, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
    Basis.dualBasis_repr, toDual_def]
/-
**LinearMap.BilinForm.apply_dualBasis_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.
BilinForm`。
形式化陈述：apply_dualBasis_left (hB : B.Nondegenerate) (b : Basis ι K V) (i j) : B (B
.dualBasis hB b i) (b j) = if j = i then 1 else 0
参数：hB : B.Nondegenerate；b : Basis ι K V；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.finiteDimensional_of_finite`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι 
: Type w}   [Finite ι] (h : Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.dualBasis.eq_1`：∀ {V : Type u_5} {K : Type u_6} [ins
t : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V] {ι : Type u_
9}   [inst_3 : Decidable…
· 使用定理 `Module.Basis.map_apply`：map_apply (i) : b.map f i = f (b i)
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Module.Basis.coe_dualBasis`：coe_dualBasis : ⇑b.dualBasis = b.coord
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.toDual_def`：toDual_def {B : BilinForm K V} (b : B.No
ndegenerate) {m n : V} : B.toDual b m n = B m n
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
-/
theorem apply_dualBasis_left (hB : B.Nondegenerate) (b : Basis ι K V) (i j) :
    B (B.dualBasis hB b i) (b j) = if j = i then 1 else 0 := by
  have := b.finiteDimensional_of_finite
  rw [dualBasis, Basis.map_apply, Basis.coe_dualBasis, ← toDual_def hB,
    LinearEquiv.apply_symm_apply, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
/-
**LinearMap.BilinForm.apply_dualBasis_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
.BilinForm`。
形式化陈述：apply_dualBasis_right (hB : B.Nondegenerate) (sym : B.IsSymm) (b : Basis ι
 K V) (i j) : B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0
参数：hB : B.Nondegenerate；sym : B.IsSymm；b : Basis ι K V；i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B : Li
nearMap.BilinForm R…
· 使用定理 `LinearMap.BilinForm.apply_dualBasis_left`：apply_dualBasis_left (hB : B.N
ondegenerate) (b : Basis ι K V) (i j) : B (B.dualBasis hB b i) (b j) = if j = i 
then 1 else 0
-/
theorem apply_dualBasis_right (hB : B.Nondegenerate) (sym : B.IsSymm)
    (b : Basis ι K V) (i j) : B (b i) (B.dualBasis hB b j) = if i = j then 1 else 0 := by
  rw [sym.eq, apply_dualBasis_left]

@[simp]
/-
**LinearMap.BilinForm.dualBasis_dualBasis_flip** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map.BilinForm`。
形式化陈述：dualBasis_dualBasis_flip (hB : B.Nondegenerate) (b : Basis ι K V) : B.dual
Basis hB (B.flip.dualBasis hB.flip b) = b
参数：hB : B.Nondegenerate；b : Basis ι K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.eq_of_apply_eq`：eq_of_apply_eq {b₁ b₂ : Basis ι R M} : (for
all i, b₁ i = b₂ i) -> b₁ = b₂
· 使用定理 `LinearMap.BilinForm.Nondegenerate.flip`：∀ {R : Type u_1} {M : Type u_2} 
[inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] 
  {B : LinearMap.BilinForm R…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LinearMap.BilinForm.Nondegenerate.ker_eq_bot`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   {B : LinearMap.BilinForm R…
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.apply_dualBasis_left`：apply_dualBasis_left (hB : B.N
ondegenerate) (b : Basis ι K V) (i j) : B (B.dualBasis hB b i) (b j) = if j = i 
then 1 else 0
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dualBasis_dualBasis_flip (hB : B.Nondegenerate) (b : Basis ι K V) :
    B.dualBasis hB (B.flip.dualBasis hB.flip b) = b := by
  ext i
  refine LinearMap.ker_eq_bot.mp hB.ker_eq_bot ((B.flip.dualBasis hB.flip b).ext (fun j ↦ ?_))
  simp_rw [apply_dualBasis_left, ← B.flip_apply, apply_dualBasis_left, @eq_comm _ i j]

@[simp]
/-
**LinearMap.BilinForm.dualBasis_flip_dualBasis** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map.BilinForm`。
形式化陈述：dualBasis_flip_dualBasis (hB : B.Nondegenerate) (b : Basis ι K V) : B.flip
.dualBasis hB.flip (B.dualBasis hB b) = b
参数：hB : B.Nondegenerate；b : Basis ι K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.BilinForm.dualBasis_dualBasis_flip`：dualBasis_dualBasis_flip (
hB : B.Nondegenerate) (b : Basis ι K V) : B.dualBasis hB (B.flip.dualBasis hB.fl
ip b) = b
· 使用定理 `LinearMap.BilinForm.Nondegenerate.flip`：∀ {R : Type u_1} {M : Type u_2} 
[inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] 
  {B : LinearMap.BilinForm R…
-/
lemma dualBasis_flip_dualBasis (hB : B.Nondegenerate) (b : Basis ι K V) :
    B.flip.dualBasis hB.flip (B.dualBasis hB b) = b :=
  dualBasis_dualBasis_flip hB.flip b

@[simp]
/-
**LinearMap.BilinForm.dualBasis_dualBasis** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.B
ilinForm`。
形式化陈述：dualBasis_dualBasis (hB : B.Nondegenerate) (hB' : B.IsSymm) (b : Basis ι K
 V) : B.dualBasis hB (B.dualBasis hB b) = b
参数：hB : B.Nondegenerate；hB' : B.IsSymm；b : Basis ι K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.Nondegenerate.flip`：∀ {R : Type u_1} {M : Type u_2} 
[inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] 
  {B : LinearMap.BilinForm R…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.BilinForm.isSymm_iff_flip`：isSymm_iff_flip : B.IsSymm ↔ flipHo
m B = B where mp
· 使用引理 `LinearMap.BilinForm.dualBasis_dualBasis_flip`：dualBasis_dualBasis_flip (
hB : B.Nondegenerate) (b : Basis ι K V) : B.dualBasis hB (B.flip.dualBasis hB.fl
ip b) = b
-/
lemma dualBasis_dualBasis (hB : B.Nondegenerate) (hB' : B.IsSymm)
    (b : Basis ι K V) :
    B.dualBasis hB (B.dualBasis hB b) = b := by
  convert! dualBasis_dualBasis_flip hB.flip b
  rwa [eq_comm, ← isSymm_iff_flip]
/-
**LinearMap.BilinForm.dualBasis_involutive** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.
BilinForm`。
形式化陈述：dualBasis_involutive (hB : B.Nondegenerate) (hB' : B.IsSymm) : Function.In
volutive (B.dualBasis hB : Basis ι K V -> Basis ι K V)
参数：hB : B.Nondegenerate；hB' : B.IsSymm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.BilinForm.dualBasis_dualBasis`：dualBasis_dualBasis (hB : B.Non
degenerate) (hB' : B.IsSymm) (b : Basis ι K V) : B.dualBasis hB (B.dualBasis hB 
b) = b
-/
lemma dualBasis_involutive (hB : B.Nondegenerate) (hB' : B.IsSymm) :
    Function.Involutive (B.dualBasis hB : Basis ι K V → Basis ι K V) :=
  fun b ↦ dualBasis_dualBasis hB hB' b
/-
**LinearMap.BilinForm.dualBasis_injective** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.B
ilinForm`。
形式化陈述：dualBasis_injective (hB : B.Nondegenerate) (hB' : B.IsSymm) : Function.Inj
ective (B.dualBasis hB : Basis ι K V -> Basis ι K V)
参数：hB : B.Nondegenerate；hB' : B.IsSymm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用引理 `LinearMap.BilinForm.dualBasis_involutive`：dualBasis_involutive (hB : B.N
ondegenerate) (hB' : B.IsSymm) : Function.Involutive (B.dualBasis hB : Basis ι K
 V -> Basis ι K V)
-/
lemma dualBasis_injective (hB : B.Nondegenerate) (hB' : B.IsSymm) :
    Function.Injective (B.dualBasis hB : Basis ι K V → Basis ι K V) :=
  (B.dualBasis_involutive hB hB').injective

@[simp]
/-
**LinearMap.BilinForm.dualBasis_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bili
nForm`。
形式化陈述：dualBasis_eq_iff (hB : B.Nondegenerate) (b : Basis ι K V) (v : ι -> V) : B
.dualBasis hB b = v ↔ forall i j, B (v i) (b j) = if j = i then 1 else 0
参数：hB : B.Nondegenerate；b : Basis ι K V；v : ι -> V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.apply_dualBasis_left`：apply_dualBasis_left (hB : B.N
ondegenerate) (b : Basis ι K V) (i j) : B (B.dualBasis hB b i) (b j) = if j = i 
then 1 else 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.ext_elem_iff`：ext_elem_iff {x y : M} : x = y ↔ forall i, b.
repr x i = b.repr y i
· 使用定理 `LinearMap.BilinForm.dualBasis_repr_apply`：dualBasis_repr_apply (hB : B.N
ondegenerate) (b : Basis ι K V) (x i) : (B.dualBasis hB b).repr x i = B x (b i)
-/
theorem dualBasis_eq_iff (hB : B.Nondegenerate) (b : Basis ι K V) (v : ι → V) :
    B.dualBasis hB b = v ↔ ∀ i j, B (v i) (b j) = if j = i then 1 else 0 :=
  ⟨fun h _ _ ↦ by rw [← h, apply_dualBasis_left],
    fun h ↦ funext fun _ ↦ (B.dualBasis hB b).ext_elem_iff.mpr fun _ ↦ by
      rw [dualBasis_repr_apply, dualBasis_repr_apply, apply_dualBasis_left, h]⟩

end DualBasis

section LinearAdjoints

variable [FiniteDimensional K V]

/-- Given bilinear forms `B₁, B₂` where `B₂` is nondegenerate, `symmCompOfNondegenerate`
is the linear map `B₂ ∘ B₁`. -/
/-
**LinearMap.BilinForm.symmCompOfNondegenerate** 是 Mathlib 中的一个定义，位于命名空间 `LinearM
ap.BilinForm`。
形式化陈述：symmCompOfNondegenerate (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate) : 
V ->ₗ[K] V
参数：B₁ B₂ : BilinForm K V；b₂ : B₂.Nondegenerate。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given bilinear forms `B₁, B₂` where `B₂` is nondegenerate, `symmCompOfNondegener
ate`
is the linear map `B₂ ∘ B₁`.
-/
noncomputable def symmCompOfNondegenerate (B₁ B₂ : BilinForm K V) (b₂ : B₂.Nondegenerate) :
    V →ₗ[K] V :=
  (B₂.toDual b₂).symm.toLinearMap.comp B₁
/-
**LinearMap.BilinForm.comp_symmCompOfNondegenerate_apply** 是 Mathlib 中的一个定理，位于命名
空间 `LinearMap.BilinForm`。
形式化陈述：comp_symmCompOfNondegenerate_apply (B₁ : BilinForm K V) {B₂ : BilinForm K 
V} (b₂ : B₂.Nondegenerate) (v : V) : B₂ (B₁.symmCompOfNondegenerate B₂ b₂ v) = B
₁ v
参数：B₁ : BilinForm K V；b₂ : B₂.Nondegenerate；v : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.symmCompOfNondegenerate.eq_1`：∀ {V : Type u_5} {K : 
Type u_6} [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V
]   [inst_3 : FiniteDimensional K V] (…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem comp_symmCompOfNondegenerate_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v : V) :
    B₂ (B₁.symmCompOfNondegenerate B₂ b₂ v) = B₁ v := by
  rw [symmCompOfNondegenerate]
  simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  erw [LinearEquiv.apply_symm_apply (B₂.toDual b₂)]

@[simp]
/-
**LinearMap.BilinForm.symmCompOfNondegenerate_left_apply** 是 Mathlib 中的一个定理，位于命名
空间 `LinearMap.BilinForm`。
形式化陈述：symmCompOfNondegenerate_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K 
V} (b₂ : B₂.Nondegenerate) (v w : V) : B₂ (symmCompOfNondegenerate B₁ B₂ b₂ w) v
 = B₁ w v
参数：B₁ : BilinForm K V；b₂ : B₂.Nondegenerate；v w : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.comp_symmCompOfNondegenerate_apply`：comp_symmCompOfN
ondegenerate_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V} (b₂ : B₂.Nondegener
ate) (v : V) : B₂ (B₁.symmCompOfNondegenerat…
-/
theorem symmCompOfNondegenerate_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (b₂ : B₂.Nondegenerate) (v w : V) : B₂ (symmCompOfNondegenerate B₁ B₂ b₂ w) v = B₁ w v := by
  conv_lhs => rw [comp_symmCompOfNondegenerate_apply]

/-- Given the nondegenerate bilinear form `B` and the linear map `φ`,
`leftAdjointOfNondegenerate` provides the left adjoint of `φ` with respect to `B`.
The lemma proving this property is `BilinForm.isAdjointPairLeftAdjointOfNondegenerate`. -/
/-
**LinearMap.BilinForm.leftAdjointOfNondegenerate** 是 Mathlib 中的一个定义，位于命名空间 `Line
arMap.BilinForm`。
形式化陈述：leftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate) (φ : 
V ->ₗ[K] V) : V ->ₗ[K] V
参数：B : BilinForm K V；b : B.Nondegenerate；φ : V ->ₗ[K] V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given the nondegenerate bilinear form `B` and the linear map `φ`,
`leftAdjointOfNondegenerate` provides the left adjoint of `φ` with respect to `B
`.
The lemma proving this property is `BilinForm.isAdjointPairLeftAdjointOfNondegen
erate`.
-/
noncomputable def leftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : V →ₗ[K] V :=
  symmCompOfNondegenerate (B.compRight φ) B b
/-
**LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate** 是 Mathlib 中的一个定理
，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：isAdjointPairLeftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondege
nerate) (φ : V ->ₗ[K] V) : IsAdjointPair B B (B.leftAdjointOfNondegenerate b φ) 
φ
参数：B : BilinForm K V；b : B.Nondegenerate；φ : V ->ₗ[K] V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.symmCompOfNondegenerate_left_apply`：symmCompOfNondeg
enerate_left_apply (B₁ : BilinForm K V) {B₂ : BilinForm K V} (b₂ : B₂.Nondegener
ate) (v w : V) : B₂ (symmCompOfNondegenerate…
-/
theorem isAdjointPairLeftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (φ : V →ₗ[K] V) : IsAdjointPair B B (B.leftAdjointOfNondegenerate b φ) φ := fun x y =>
  (B.compRight φ).symmCompOfNondegenerate_left_apply b y x

/-- Given the nondegenerate bilinear form `B`, the linear map `φ` has a unique left adjoint given by
`BilinForm.leftAdjointOfNondegenerate`. -/
/-
**LinearMap.BilinForm.isAdjointPair_iff_eq_of_nondegenerate** 是 Mathlib 中的一个定理，位
于命名空间 `LinearMap.BilinForm`。
形式化陈述：isAdjointPair_iff_eq_of_nondegenerate (B : BilinForm K V) (b : B.Nondegene
rate) (ψ φ : V ->ₗ[K] V) : IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfNondegener
ate b φ
参数：B : BilinForm K V；b : B.Nondegenerate；ψ φ : V ->ₗ[K] V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.isAdjointPair_unique_of_nondegenerate`：isAdjointPair
_unique_of_nondegenerate (B : BilinForm R₁ M₁) (b : B.Nondegenerate) (φ ψ₁ ψ₂ : 
M₁ ->ₗ[R₁] M₁) (hψ₁ : IsAdjointPair B B ψ₁ φ) (…
· 使用定理 `LinearMap.BilinForm.isAdjointPairLeftAdjointOfNondegenerate`：isAdjointPa
irLeftAdjointOfNondegenerate (B : BilinForm K V) (b : B.Nondegenerate) (φ : V ->
ₗ[K] V) : IsAdjointPair B B (B.leftAdjointOfNonde…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given the nondegenerate bilinear form `B`, the linear map `φ` has a unique left 
adjoint given by
`BilinForm.leftAdjointOfNondegenerate`.
-/
theorem isAdjointPair_iff_eq_of_nondegenerate (B : BilinForm K V) (b : B.Nondegenerate)
    (ψ φ : V →ₗ[K] V) : IsAdjointPair B B ψ φ ↔ ψ = B.leftAdjointOfNondegenerate b φ :=
  ⟨fun h =>
    B.isAdjointPair_unique_of_nondegenerate b φ ψ _ h
      (isAdjointPairLeftAdjointOfNondegenerate _ _ _),
    fun h => h.symm ▸ isAdjointPairLeftAdjointOfNondegenerate _ _ _⟩

end LinearAdjoints

end BilinForm

end LinearMap

