/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Defs
public import Mathlib.Analysis.CStarAlgebra.Module.Synonym
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Bilipschitz
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Constructions of Hilbert C⋆-modules

In this file we define the following constructions of `CStarModule`s where `A` denotes a C⋆-algebra.
For some of the types listed below, the instance is declared on the type synonym `WithCStarModule E`
(with the notation `C⋆ᵐᵒᵈ E`), instead of on `E` itself; we explain the reasoning behind each
decision below.

1. `A` as a `CStarModule` over itself.
2. `C⋆ᵐᵒᵈ(A, E × F)` as a `CStarModule` over `A`, when `E` and `F` are themselves `CStarModule`s
  over `A`.
3. `C⋆ᵐᵒᵈ (A, Π i : ι, E i)` as a `CStarModule` over `A`, when each `E i` is a `CStarModule` over
  `A` and `ι` is a `Fintype`.
4. `E` as a `CStarModule` over `ℂ`, when `E` is an `InnerProductSpace` over `ℂ`.

For `E × F` and `Π i : ι, E i`, we are required to declare the instance on a type synonym rather
than on the product or pi-type itself because the existing norm on these types does not agree with
the one induced by the C⋆-module structure. Moreover, the norm induced by the C⋆-module structure
doesn't agree with any other natural norm on these types (e.g., `WithLp 2 (E × F)` unless `A := ℂ`),
so we need a new synonym.

On `A` (a C⋆-algebra) and `E` (an inner product space), we declare the instances on the types
themselves to ease the use of the C⋆-module structure. This does have the potential to cause
inconvenience (as sometimes Lean will see terms of type `A` and apply lemmas pertaining to
C⋆-modules to those terms, when the lemmas were actually intended for terms of some other
C⋆-module in context, say `F`, in which case the arguments must be provided explicitly; see for
instance the application of `CStarModule.norm_eq_sqrt_norm_inner_self` in the proof of
`WithCStarModule.max_le_prod_norm` below). However, we believe that this, hopefully rare,
inconvenience is outweighed by avoiding translating between type synonyms where possible.

For more details on the importance of the `WithCStarModule` type synonym, see the module
documentation for `Analysis.CStarAlgebra.Module.Synonym`.

## Implementation notes

When `A := ℂ` and `E := ℂ`, then `ℂ` is both a C⋆-algebra (so it inherits a `CStarModule` instance
via (1) above) and an inner product space (so it inherits a `CStarModule` instance via (4) above).
We provide a sanity check ensuring that these two instances are definitionally equal. We also ensure
that the `Inner ℂ ℂ` instance from `InnerProductSpace` is definitionally equal to the one inherited
from the `CStarModule` instances.

Note that `C⋆ᵐᵒᵈ(A, E)` is *already* equipped with a bornology and uniformity whenever `E` is
(namely, the pullback of the respective structures through `WithCStarModule.equiv`), so in each of
the above cases, it is necessary to temporarily instantiate `C⋆ᵐᵒᵈ(A, E)` with
`CStarModule.normedAddCommGroup`, show the resulting type is bilipschitz equivalent to `E` via
`WithCStarModule.equiv` (in the first and last case, this map is actually trivially an isometry),
and then replace the uniformity and bornology with the correct ones.

-/

@[expose] public section

open CStarModule CStarRing

namespace WithCStarModule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-! ## A C⋆-algebra as a C⋆-module over itself -/

section Self

variable [StarOrderedRing A]

/-- Reinterpret a C⋆-algebra `A` as a `CStarModule` over itself. -/
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a C⋆-algebra `A` as a `CStarModule` over itself.
-/
instance : CStarModule A A where
  inner x y := y * star x
  inner_add_right := add_mul ..
  inner_self_nonneg := mul_star_self_nonneg _
  inner_self := CStarRing.mul_star_self_eq_zero_iff _
  inner_op_smul_right := mul_assoc ..
  inner_smul_right_complex := smul_mul_assoc ..
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity)]
    simpa [sq] using Eq.symm <| CStarRing.norm_self_mul_star

open scoped InnerProductSpace in
/-
**WithCStarModule.inner_def** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：inner_def (x y : A) : ⟪x, y⟫_A = y * star x
参数：x y : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inner_def (x y : A) : ⟪x, y⟫_A = y * star x := rfl

end Self

/-! ## Products of C⋆-modules -/

section Prod

open scoped InnerProductSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [Module ℂ E] [SMul A E]
variable [NormedAddCommGroup F] [Module ℂ F] [SMul A F]
variable [CStarModule A E] [CStarModule A F]

/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Norm C⋆ᵐᵒᵈ(A, E × F) where
  norm x := √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖
/-
**WithCStarModule.prod_norm** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：prod_norm (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ = √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖
参数：x : C⋆ᵐᵒᵈ(A, E × F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_norm (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ = √‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖ := rfl
/-
**WithCStarModule.prod_norm_sq** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：prod_norm_sq (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ ^ 2 = ‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_
A‖
参数：x : C⋆ᵐᵒᵈ(A, E × F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma prod_norm_sq (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ ^ 2 = ‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖ := by
  simp [prod_norm]
/-
**WithCStarModule.prod_norm_le_norm_add** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModu
le`。
形式化陈述：prod_norm_le_norm_add (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ <= ‖x.1‖ + ‖x.2‖
参数：x : C⋆ᵐᵒᵈ(A, E × F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `abs_le_of_sq_le_sq'`：abs_le_of_sq_le_sq' (h : a ^ 2 <= b ^ 2) (hb : 0 <=
 b) : -b <= a ∧ a <= b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithCStarModule.prod_norm_sq`：prod_norm_sq (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ ^
 2 = ‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CStarModule.norm_sq_eq`：norm_sq_eq {x : E} : ‖x‖ ^ 2 = ‖⟪x, x⟫‖
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 60 条，此处仅展示前 30 条）
-/
lemma prod_norm_le_norm_add (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ ≤ ‖x.1‖ + ‖x.2‖ := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  calc ‖x‖ ^ 2 ≤ ‖⟪x.1, x.1⟫_A‖ + ‖⟪x.2, x.2⟫_A‖ := prod_norm_sq x ▸ norm_add_le _ _
    _ = ‖x.1‖ ^ 2 + 0 + ‖x.2‖ ^ 2 := by simp [norm_sq_eq A]
    _ ≤ ‖x.1‖ ^ 2 + 2 * ‖x.1‖ * ‖x.2‖ + ‖x.2‖ ^ 2 := by gcongr; positivity
    _ = (‖x.1‖ + ‖x.2‖) ^ 2 := by ring

variable [StarOrderedRing A]
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CStarModule A C⋆ᵐᵒᵈ(A, E × F) where
  inner x y := ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A
  inner_add_right {x y z} := by simpa using add_add_add_comm ..
  inner_self_nonneg := add_nonneg CStarModule.inner_self_nonneg CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    apply equiv A (E × F) |>.injective
    ext
    · refine inner_self.mp <| le_antisymm ?_ (inner_self_nonneg (A := A))
      exact le_add_of_nonneg_right CStarModule.inner_self_nonneg |>.trans_eq h
    · refine inner_self.mp <| le_antisymm ?_ (inner_self_nonneg (A := A))
      exact le_add_of_nonneg_left CStarModule.inner_self_nonneg |>.trans_eq h
  inner_op_smul_right := by simp [mul_add]
  inner_smul_right_complex := by simp [smul_add]
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by with_reducible_and_instances rfl
/-
**WithCStarModule.prod_inner** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：prod_inner (x y : C⋆ᵐᵒᵈ(A, E × F)) : ⟪x, y⟫_A = ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_
A
参数：x y : C⋆ᵐᵒᵈ(A, E × F)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma prod_inner (x y : C⋆ᵐᵒᵈ(A, E × F)) : ⟪x, y⟫_A = ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A := rfl
/-
**WithCStarModule.max_le_prod_norm** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：max_le_prod_norm (x : C⋆ᵐᵒᵈ(A, E × F)) : max ‖x.1‖ ‖x.2‖ <= ‖x‖
参数：x : C⋆ᵐᵒᵈ(A, E × F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithCStarModule.prod_norm`：prod_norm (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ = √‖⟪x.
1, x.1⟫_A + ⟪x.2, x.2⟫_A‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CStarModule.norm_eq_sqrt_norm_inner_self`：∀ {A : Type u_1} {E : Type u_2
} {inst : NonUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A
}   {inst_3 : AddCommGroup E} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `CStarAlgebra.norm_le_norm_of_nonneg_of_le`：norm_le_norm_of_nonneg_of_le 
{a b : A} (ha : 0 <= a
· 使用定理 `CStarModule.inner_self_nonneg`：∀ {A : Type u_1} {E : Type u_2} {inst : N
onUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3
 : AddCommGroup E} …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLT`：∀ {α : Type u_1} [inst : Ad
dCommMonoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], AddLeftRe
flectLT α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
-/
lemma max_le_prod_norm (x : C⋆ᵐᵒᵈ(A, E × F)) : max ‖x.1‖ ‖x.2‖ ≤ ‖x‖ := by
  rw [prod_norm]
  simp only [norm_eq_sqrt_norm_inner_self (A := A) (E := E),
    norm_eq_sqrt_norm_inner_self (A := A) (E := F), max_le_iff, norm_nonneg,
    Real.sqrt_le_sqrt_iff]
  constructor
  all_goals
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (A := A) ?_ ?_
    all_goals
      aesop (add safe apply CStarModule.inner_self_nonneg)
/-
**WithCStarModule.norm_equiv_le_norm_prod** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarMo
dule`。
形式化陈述：norm_equiv_le_norm_prod (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖equiv A (E × F) x‖ <= ‖x‖
参数：x : C⋆ᵐᵒᵈ(A, E × F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `WithCStarModule.max_le_prod_norm`：max_le_prod_norm (x : C⋆ᵐᵒᵈ(A, E × F))
 : max ‖x.1‖ ‖x.2‖ <= ‖x‖
-/
lemma norm_equiv_le_norm_prod (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖equiv A (E × F) x‖ ≤ ‖x‖ :=
  max_le_prod_norm x

section Aux

-- We temporarily disable the uniform space and bornology on `C⋆ᵐᵒᵈ A` while proving
-- that those induced by the new norm are equal to the old ones.
attribute [-instance] WithCStarModule.instUniformSpace WithCStarModule.instBornology

/-- A normed additive commutative group structure on `C⋆ᵐᵒᵈ(A, E × F)` with the wrong topology,
uniformity and bornology. This is only used to build the instance with the correct forgetful
inheritance data. -/
@[instance_reducible]
/-
**WithCStarModule.normedAddCommGroupProdAux** 是 Mathlib 中的一个定义，位于命名空间 `WithCStar
Module`。
形式化陈述：normedAddCommGroupProdAux : NormedAddCommGroup C⋆ᵐᵒᵈ(A, E × F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed additive commutative group structure on `C⋆ᵐᵒᵈ(A, E × F)` with the wron
g topology,
uniformity and bornology. This is only used to build the instance with the corre
ct forgetful
inheritance data.
-/
noncomputable def normedAddCommGroupProdAux : NormedAddCommGroup C⋆ᵐᵒᵈ(A, E × F) :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

attribute [local instance] normedAddCommGroupProdAux

open Filter Uniformity Bornology
/-
**WithCStarModule.antilipschitzWith_two_equiv_prod_aux** 是 Mathlib 中的一个引理，位于命名空间
 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma antilipschitzWith_two_equiv_prod_aux : AntilipschitzWith 2 (equiv A (E × F)) :=
  AddMonoidHomClass.antilipschitz_of_bound (linearEquiv ℂ A (E × F)) fun x ↦ by
    apply prod_norm_le_norm_add x |>.trans
    simp only [NNReal.coe_ofNat, linearEquiv_apply, two_mul]
    gcongr
    · exact norm_fst_le x
    · exact norm_snd_le x
/-
**WithCStarModule.lipschitzWith_one_equiv_prod_aux** 是 Mathlib 中的一个引理，位于命名空间 `Wi
thCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma lipschitzWith_one_equiv_prod_aux : LipschitzWith 1 (equiv A (E × F)) :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm (linearEquiv ℂ A (E × F)) 1 <| by
    simpa using! norm_equiv_le_norm_prod
/-
**WithCStarModule.uniformity_prod_eq_aux** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarMod
ule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma uniformity_prod_eq_aux :
    𝓤[(inferInstance : UniformSpace (E × F)).comap <| equiv _ _] = 𝓤 C⋆ᵐᵒᵈ(A, E × F) :=
  uniformity_eq_of_bilipschitz antilipschitzWith_two_equiv_prod_aux lipschitzWith_one_equiv_prod_aux
/-
**WithCStarModule.isBounded_prod_iff_aux** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarMod
ule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isBounded_prod_iff_aux (s : Set C⋆ᵐᵒᵈ(A, E × F)) :
    @IsBounded _ (induced <| equiv A (E × F)) s ↔ IsBounded s :=
  isBounded_iff_of_bilipschitz antilipschitzWith_two_equiv_prod_aux
    lipschitzWith_one_equiv_prod_aux s

end Aux

/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : NormedAddCommGroup C⋆ᵐᵒᵈ(A, E × F) :=
  fast_instance% .ofCoreReplaceAll (normedSpaceCore A) ?_ ?_
where finally
  exacts [uniformity_prod_eq_aux, isBounded_prod_iff_aux]
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : NormedSpace ℂ C⋆ᵐᵒᵈ(A, E × F) := .ofCore (normedSpaceCore A)

end Prod

/-! ## Pi-types of C⋆-modules -/

section Pi

open scoped InnerProductSpace

variable {ι : Type*} {E : ι → Type*} [Fintype ι]
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, SMul A (E i)]
variable [∀ i, CStarModule A (E i)]

/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Norm C⋆ᵐᵒᵈ(A, Π i, E i) where
  norm x := √‖∑ i, ⟪x i, x i⟫_A‖
/-
**WithCStarModule.pi_norm** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：pi_norm (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ = √‖∑ i, ⟪x i, x i⟫_A‖
参数：x : C⋆ᵐᵒᵈ(A, Π i, E i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pi_norm (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ = √‖∑ i, ⟪x i, x i⟫_A‖ := by
  with_reducible_and_instances rfl
/-
**WithCStarModule.pi_norm_sq** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：pi_norm_sq (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ ^ 2 = ‖∑ i, ⟪x i, x i⟫_A‖
参数：x : C⋆ᵐᵒᵈ(A, Π i, E i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithCStarModule.pi_norm`：pi_norm (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ = √‖∑ i,
 ⟪x i, x i⟫_A‖
· 使用定理 `Real.sq_sqrt`：sq_sqrt (h : 0 <= x) : √x ^ 2 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pi_norm_sq (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ ^ 2 = ‖∑ i, ⟪x i, x i⟫_A‖ := by
  simp [pi_norm]

open Finset in
/-
**WithCStarModule.pi_norm_le_sum_norm** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule
`。
形式化陈述：pi_norm_le_sum_norm (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ <= ∑ i, ‖x i‖
参数：x : C⋆ᵐᵒᵈ(A, Π i, E i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `abs_le_of_sq_le_sq'`：abs_le_of_sq_le_sq' (h : a ^ 2 <= b ^ 2) (hb : 0 <=
 b) : -b <= a ∧ a <= b
· 使用定理 `norm_sum_le`：norm_sum_le {E} [SeminormedAddCommGroup E] (s : Finset ι) (
f : ι -> E) : ‖∑ i in s, f i‖ <= ∑ i in s, ‖f i‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithCStarModule.pi_norm_sq`：pi_norm_sq (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ ^ 
2 = ‖∑ i, ⟪x i, x i⟫_A‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `CStarModule.norm_sq_eq`：norm_sq_eq {x : E} : ‖x‖ ^ 2 = ‖⟪x, x⟫‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.sum_sq_le_sq_sum_of_nonneg`：sum_sq_le_sq_sum_of_nonneg (hf : fora
ll i in s, 0 <= f i) : ∑ i in s, f i ^ 2 <= (∑ i in s, f i) ^ 2
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma pi_norm_le_sum_norm (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  calc ‖x‖ ^ 2 ≤ ∑ i, ‖⟪x i, x i⟫_A‖ := pi_norm_sq x ▸ norm_sum_le _ _
    _ = ∑ i, ‖x i‖ ^ 2 := by simp only [norm_sq_eq A]
    _ ≤ (∑ i, ‖x i‖) ^ 2 := sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)

variable [StarOrderedRing A]

open Finset in
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : CStarModule A C⋆ᵐᵒᵈ(A, Π i, E i) where
  inner x y := ∑ i, ⟪x i, y i⟫_A
  inner_add_right {x y z} := by simp [sum_add_distrib]
  inner_self_nonneg := sum_nonneg <| fun _ _ ↦ CStarModule.inner_self_nonneg
  inner_self {x} := by
    refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
    ext i
    refine inner_self.mp <| le_antisymm (le_of_le_of_eq ?_ h) inner_self_nonneg
    exact single_le_sum (fun i _ ↦ CStarModule.inner_self_nonneg (A := A) (x := x i)) (mem_univ _)
  inner_op_smul_right := by simp [mul_sum]
  inner_smul_right_complex := by simp [smul_sum]
  star_inner x y := by simp
  norm_eq_sqrt_norm_inner_self {x} := by with_reducible_and_instances rfl
/-
**WithCStarModule.pi_inner** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：pi_inner (x y : C⋆ᵐᵒᵈ(A, Π i, E i)) : ⟪x, y⟫_A = ∑ i, ⟪x i, y i⟫_A
参数：x y : C⋆ᵐᵒᵈ(A, Π i, E i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma pi_inner (x y : C⋆ᵐᵒᵈ(A, Π i, E i)) : ⟪x, y⟫_A = ∑ i, ⟪x i, y i⟫_A := rfl

@[simp]
/-
**WithCStarModule.inner_single_left** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：inner_single_left [DecidableEq ι] (x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E 
i) : .symm Pi.single i y, x⟫_A = ⟪y, x i⟫_A
参数：x : C⋆ᵐᵒᵈ(A, Π i, E i)；y : E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CStarModule.inner_zero_left`：∀ {A : Type u_1} {E : Type u_2} [inst : Non
UnitalRing A] [inst_1 : StarRing A] [inst_2 : AddCommGroup E]   [inst_3 : _root_
.Module ℂ A] [ins…
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
lemma inner_single_left [DecidableEq ι] (x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E i) :
    ⟪equiv _ _ |>.symm <| Pi.single i y, x⟫_A = ⟪y, x i⟫_A := by
  simp only [pi_inner, equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  all_goals simp_all

@[simp]
/-
**WithCStarModule.inner_single_right** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`
。
形式化陈述：inner_single_right [DecidableEq ι] (x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E
 i) : .symm Pi.single i y⟫_A = ⟪x i, y⟫_A
参数：x : C⋆ᵐᵒᵈ(A, Π i, E i)；y : E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CStarModule.inner_zero_right`：∀ {A : Type u_1} {E : Type u_2} [inst : No
nUnitalRing A] [inst_1 : StarRing A] [inst_2 : AddCommGroup E]   [inst_3 : _root
_.Module ℂ A] [ins…
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
lemma inner_single_right [DecidableEq ι] (x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E i) :
    ⟪x, equiv _ _ |>.symm <| Pi.single i y⟫_A = ⟪x i, y⟫_A := by
  simp only [pi_inner, equiv_symm_pi_apply]
  rw [Finset.sum_eq_single i]
  all_goals simp_all

@[simp]
/-
**WithCStarModule.norm_single** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`。
形式化陈述：norm_single [DecidableEq ι] (i : ι) (y : E i) : .symm Pi.single i y‖ = ‖y‖
参数：i : ι；y : E i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CStarModule.norm_sq_eq`：norm_sq_eq {x : E} : ‖x‖ ^ 2 = ‖⟪x, x⟫‖
· 使用引理 `WithCStarModule.inner_single_right`：inner_single_right [DecidableEq ι] (
x : C⋆ᵐᵒᵈ(A, Π i, E i)) {i : ι} (y : E i) : .symm Pi.single i y⟫_A = ⟪x i, y⟫_A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_single [DecidableEq ι] (i : ι) (y : E i) :
    ‖equiv A _ |>.symm <| Pi.single i y‖ = ‖y‖ := by
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
  rw [← sq_eq_sq₀ (by positivity) (by positivity)]
  simp [norm_sq_eq A]
/-
**WithCStarModule.norm_apply_le_norm** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModule`
。
形式化陈述：norm_apply_le_norm (x : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι) : ‖x i‖ <= ‖x‖
参数：x : C⋆ᵐᵒᵈ(A, Π i, E i)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `abs_le_of_sq_le_sq'`：abs_le_of_sq_le_sq' (h : a ^ 2 <= b ^ 2) (hb : 0 <=
 b) : -b <= a ∧ a <= b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithCStarModule.pi_norm_sq`：pi_norm_sq (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖x‖ ^ 
2 = ‖∑ i, ⟪x i, x i⟫_A‖
· 使用引理 `CStarModule.norm_sq_eq`：norm_sq_eq {x : E} : ‖x‖ ^ 2 = ‖⟪x, x⟫‖
· 使用引理 `CStarAlgebra.norm_le_norm_of_nonneg_of_le`：norm_le_norm_of_nonneg_of_le 
{a b : A} (ha : 0 <= a
· 使用定理 `CStarModule.inner_self_nonneg`：∀ {A : Type u_1} {E : Type u_2} {inst : N
onUnitalSemiring A} {inst_1 : StarRing A} {inst_2 : _root_.Module ℂ A}   {inst_3
 : AddCommGroup E} …
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedCancelAddMonoid.toIsOrderedAddMonoid`：∀ {α : Type u_2} {inst : 
AddCommMonoid α} {inst_1 : Preorder α} [self : IsOrderedCancelAddMonoid α],   Is
OrderedAddMonoid α
· 使用定理 `IsOrderedAddMonoid.toIsOrderedCancelAddMonoid`：∀ {α : Type u} [inst : Ad
dCommGroup α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], IsOrderedCancelAddMo
noid α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
lemma norm_apply_le_norm (x : C⋆ᵐᵒᵈ(A, Π i, E i)) (i : ι) : ‖x i‖ ≤ ‖x‖ := by
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  rw [pi_norm_sq, norm_sq_eq A]
  refine CStarAlgebra.norm_le_norm_of_nonneg_of_le inner_self_nonneg ?_
  exact Finset.single_le_sum (fun j _ ↦ inner_self_nonneg (A := A) (x := x j)) (Finset.mem_univ i)

open Finset in
/-
**WithCStarModule.norm_equiv_le_norm_pi** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModu
le`。
形式化陈述：norm_equiv_le_norm_pi (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖equiv _ _ x‖ <= ‖x‖
参数：x : C⋆ᵐᵒᵈ(A, Π i, E i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pi_norm_le_iff_of_nonneg`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fi
ntype ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r 
: ℝ}, 0 ≤ r → …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `WithCStarModule.norm_apply_le_norm`：norm_apply_le_norm (x : C⋆ᵐᵒᵈ(A, Π i
, E i)) (i : ι) : ‖x i‖ <= ‖x‖
-/
lemma norm_equiv_le_norm_pi (x : C⋆ᵐᵒᵈ(A, Π i, E i)) : ‖equiv _ _ x‖ ≤ ‖x‖ := by
  let _ : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) := normedAddCommGroup A
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  simpa using norm_apply_le_norm x

section Aux

-- We temporarily disable the uniform space and bornology on `C⋆ᵐᵒᵈ A` while proving
-- that those induced by the new norm are equal to the old ones.
attribute [-instance] WithCStarModule.instUniformSpace WithCStarModule.instBornology

/-- A normed additive commutative group structure on `C⋆ᵐᵒᵈ(A, Π i, E i)` with the wrong topology,
uniformity and bornology. This is only used to build the instance with the correct forgetful
inheritance data. -/
@[instance_reducible]
/-
**WithCStarModule.normedAddCommGroupPiAux** 是 Mathlib 中的一个定义，位于命名空间 `WithCStarMo
dule`。
形式化陈述：normedAddCommGroupPiAux : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed additive commutative group structure on `C⋆ᵐᵒᵈ(A, Π i, E i)` with the w
rong topology,
uniformity and bornology. This is only used to build the instance with the corre
ct forgetful
inheritance data.
-/
noncomputable def normedAddCommGroupPiAux : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) :=
  NormedAddCommGroup.ofCore (CStarModule.normedSpaceCore A)

attribute [local instance] normedAddCommGroupPiAux

open Uniformity Bornology
/-
**WithCStarModule.antilipschitzWith_card_equiv_pi_aux** 是 Mathlib 中的一个引理，位于命名空间 
`WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma antilipschitzWith_card_equiv_pi_aux :
    AntilipschitzWith (Fintype.card ι) (equiv A (Π i, E i)) :=
  AddMonoidHomClass.antilipschitz_of_bound (linearEquiv ℂ A (Π i, E i)) fun x ↦ by
    simp only [NNReal.coe_natCast, linearEquiv_apply]
    calc ‖x‖ ≤ ∑ i, ‖x i‖ := pi_norm_le_sum_norm x
      _ ≤ ∑ _, ‖⇑x‖ := Finset.sum_le_sum fun _ _ ↦ norm_le_pi_norm ..
      _ ≤ Fintype.card ι * ‖⇑x‖ := by simp
/-
**WithCStarModule.lipschitzWith_one_equiv_pi_aux** 是 Mathlib 中的一个引理，位于命名空间 `With
CStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma lipschitzWith_one_equiv_pi_aux : LipschitzWith 1 (equiv A (Π i, E i)) :=
  AddMonoidHomClass.lipschitz_of_bound_nnnorm (linearEquiv ℂ A (Π i, E i)) 1 <| by
    simpa using! norm_equiv_le_norm_pi
/-
**WithCStarModule.uniformity_pi_eq_aux** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModul
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma uniformity_pi_eq_aux :
    𝓤[(inferInstance : UniformSpace (Π i, E i)).comap <| equiv A _] = 𝓤 C⋆ᵐᵒᵈ(A, Π i, E i) :=
  uniformity_eq_of_bilipschitz antilipschitzWith_card_equiv_pi_aux lipschitzWith_one_equiv_pi_aux
/-
**WithCStarModule.isBounded_pi_iff_aux** 是 Mathlib 中的一个引理，位于命名空间 `WithCStarModul
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isBounded_pi_iff_aux (s : Set C⋆ᵐᵒᵈ(A, Π i, E i)) :
    @IsBounded _ (induced <| equiv A (Π i, E i)) s ↔ IsBounded s :=
  isBounded_iff_of_bilipschitz antilipschitzWith_card_equiv_pi_aux lipschitzWith_one_equiv_pi_aux s

end Aux

/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : NormedAddCommGroup C⋆ᵐᵒᵈ(A, Π i, E i) :=
  fast_instance% .ofCoreReplaceAll (normedSpaceCore A) ?_ ?_
where finally
  exacts [uniformity_pi_eq_aux, isBounded_pi_iff_aux]
/-
**WithCStarModule.** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : NormedSpace ℂ C⋆ᵐᵒᵈ(A, Π i, E i) := .ofCore (normedSpaceCore A)

end Pi

/-! ## Inner product spaces as C⋆-modules -/

section InnerProductSpace

open ComplexOrder

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open scoped InnerProductSpace in
/-- Reinterpret an inner product space `E` over `ℂ` as a `CStarModule` over `ℂ`.

Note: this instance requires `SMul ℂᵐᵒᵖ E` and `IsCentralScalar ℂ E` instances to exist on `E`,
which is unlikely to occur in practice. However, in practice one could either add those instances
to the type `E` in question, or else supply them to this instance manually, which is reason behind
the naming of these two instance arguments. -/
/-
**WithCStarModule.instCStarModuleComplex** 是 Mathlib 中的一个实例，位于命名空间 `WithCStarMod
ule`。
形式化陈述：instCStarModuleComplex : CStarModule Complex E where inner x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an inner product space `E` over `ℂ` as a `CStarModule` over `ℂ`.

Note: this instance requires `SMul ℂᵐᵒᵖ E` and `IsCentralScalar ℂ E` instances t
o exist on `E`,
which is unlikely to occur in practice. However, in practice one could either ad
d those instances
to the type `E` in question, or else supply them to this instance manually, whic
h is reason behind
the naming of these two instance arguments.
-/
noncomputable instance instCStarModuleComplex : CStarModule ℂ E where
  inner x y := ⟪x, y⟫_ℂ
  inner_add_right := by simp [_root_.inner_add_right]
  inner_self_nonneg {x} := by
    rw [← inner_self_ofReal_re, RCLike.ofReal_nonneg]
    exact inner_self_nonneg
  inner_self := by simp
  inner_op_smul_right := by simp [inner_smul_right]
  inner_smul_right_complex := by simp [inner_smul_right, smul_eq_mul]
  star_inner _ _ := by simp
  norm_eq_sqrt_norm_inner_self {x} := by
    simpa only [← inner_self_re_eq_norm] using norm_eq_sqrt_re_inner x

-- Ensures that the two ways to obtain `CStarModule ℂᵐᵒᵖ ℂ` are definitionally equal.
/-
**WithCStarModule.** 是 Mathlib 中的一个示例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : instCStarModule (A := ℂ) = instCStarModuleComplex := by with_reducible_and_instances rfl

/-- Ensures that the two `Inner ℂ ℂ` instances are definitionally equal. Note that this cannot be at
reducible and instances transparency because the one from `InnerProductSpace` uses `StarRingEnd`
whereas `WithCStarModule.instCStarModule.toInner` uses `star` since `A` may not be commutative. -/
/-
**WithCStarModule.** 是 Mathlib 中的一个示例，位于命名空间 `WithCStarModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ensures that the two `Inner ℂ ℂ` instances are definitionally equal. Note that t
his cannot be at
reducible and instances transparency because the one from `InnerProductSpace` us
es `StarRingEnd`
whereas `WithCStarModule.instCStarModule.toInner` uses `star` since `A` may not 
be commutative.
-/
example : (toInner : Inner ℂ ℂ) = WithCStarModule.instCStarModule.toInner := rfl

end InnerProductSpace

end WithCStarModule

