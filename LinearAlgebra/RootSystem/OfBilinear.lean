/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Defs

/-!
# Root pairings made from bilinear forms

A common construction of root systems is given by taking the set of all vectors in an integral
lattice for which reflection yields an automorphism of the lattice.  In this file, we generalize
this construction, replacing the ring of integers with an arbitrary commutative ring and the
integral lattice with an arbitrary reflexive module equipped with a bilinear form.

## Main definitions:
* `LinearMap.IsReflective`: Length is a regular value of `R`, and reflection is definable.
* `LinearMap.IsReflective.coroot`: The coroot corresponding to a reflective vector.
* `RootPairing.of_Bilinear`: The root pairing whose roots are reflective vectors.

## TODO
* properties
-/

@[expose] public section

open Set Function Module

noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

namespace LinearMap

/-- A vector `x` is reflective with respect to a bilinear form if multiplication by its norm is
injective, and for any vector `y`, the norm of `x` divides twice the inner product of `x` and `y`.
These conditions are what we need when describing reflection as a map taking `y` to
`y - 2 • (B x y) / (B x x) • x`. -/
/-
**LinearMap.IsReflective** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommRing R] → [inst_1 : Ad
dCommGroup M] → [inst_2 : _root_.Module R M] → (M →ₗ[R] M →ₗ[R] R) → M → Prop
参数：M →ₗ[R] M →ₗ[R] R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A vector `x` is reflective with respect to a bilinear form if multiplication by 
its norm is
injective, and for any vector `y`, the norm of `x` divides twice the inner produ
ct of `x` and `y`.
These conditions are what we need when describing reflection as a map taking `y`
 to
`y - 2 • (B x y) / (B x x) • x`.
-/
structure IsReflective (B : M →ₗ[R] M →ₗ[R] R) (x : M) : Prop where
  regular : IsRegular (B x x)
  dvd_two_mul : ∀ y, B x x ∣ 2 * B x y

variable (B : M →ₗ[R] M →ₗ[R] R) {x : M}

namespace IsReflective

/-
**LinearMap.IsReflective.of_dvd_two** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.IsRefle
ctive`。
形式化陈述：of_dvd_two [IsCancelMulZero R] [NeZero (2 : R)] (hx : B x x ∣ 2) : IsRefle
ctive B x where regular
参数：2 : R；hx : B x x ∣ 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsRegular.of_ne_zero`：IsRegular.of_ne_zero (a0 : a != 0) : IsRegular a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
-/
lemma of_dvd_two [IsCancelMulZero R] [NeZero (2 : R)] (hx : B x x ∣ 2) :
    IsReflective B x where
  regular := .of_ne_zero <| fun contra ↦ by simp [contra, two_ne_zero (α := R)] at hx
  dvd_two_mul y := hx.mul_right (B x y)

variable (hx : IsReflective B x)

/-- The coroot attached to a reflective vector. -/
/-
**LinearMap.IsReflective.coroot** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.IsReflectiv
e`。
形式化陈述：coroot : M ->ₗ[R] R where toFun y
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsReflective.dvd_two_mul`：∀ {R : Type u_1} {M : Type u_2} [ins
t : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {B : M 
→ₗ[R] M →ₗ[R] R} {x : M}…

--- 原说明 ---
The coroot attached to a reflective vector.
-/
def coroot : M →ₗ[R] R where
  toFun y := (hx.2 y).choose
  map_add' a b := by
    refine hx.1.1 ?_
    simp only
    rw [← (hx.2 (a + b)).choose_spec, mul_add, ← (hx.2 a).choose_spec, ← (hx.2 b).choose_spec,
      map_add, mul_add]
  map_smul' r a := by
    refine hx.1.1 ?_
    simp only [RingHom.id_apply]
    rw [← (hx.2 (r • a)).choose_spec, smul_eq_mul, mul_left_comm, ← (hx.2 a).choose_spec, map_smul,
      two_mul, smul_eq_mul, two_mul, mul_add]

@[simp]
/-
**LinearMap.IsReflective.apply_self_mul_coroot_apply** 是 Mathlib 中的一个引理，位于命名空间 `
LinearMap.IsReflective`。
形式化陈述：apply_self_mul_coroot_apply {y : M} : B x x * coroot B hx y = 2 * B x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.IsReflective.dvd_two_mul`：∀ {R : Type u_1} {M : Type u_2} [ins
t : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {B : M 
→ₗ[R] M →ₗ[R] R} {x : M}…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma apply_self_mul_coroot_apply {y : M} : B x x * coroot B hx y = 2 * B x y :=
  (hx.dvd_two_mul y).choose_spec.symm

@[simp]
/-
**LinearMap.IsReflective.smul_coroot** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.IsRefl
ective`。
形式化陈述：smul_coroot : B x x • coroot B hx = 2 • B x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.IsReflective.apply_self_mul_coroot_apply`：apply_self_mul_coroo
t_apply {y : M} : B x x * coroot B hx y = 2 * B x y
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma smul_coroot : B x x • coroot B hx = 2 • B x := by
  ext y
  simp [smul_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat, apply_self_mul_coroot_apply]

@[simp]
/-
**LinearMap.IsReflective.coroot_apply_self** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.
IsReflective`。
形式化陈述：coroot_apply_self : coroot B hx x = 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `LinearMap.IsReflective.regular`：∀ {R : Type u_1} {M : Type u_2} [inst : 
CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {B : M →ₗ[R
] M →ₗ[R] R} {x : M}…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.IsReflective.apply_self_mul_coroot_apply`：apply_self_mul_coroo
t_apply {y : M} : B x x * coroot B hx y = 2 * B x y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coroot_apply_self : coroot B hx x = 2 :=
  hx.regular.left <| by simp [mul_comm _ (B x x)]

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.IsReflective.isOrthogonal_reflection** 是 Mathlib 中的一个引理，位于命名空间 `Line
arMap.IsReflective`。
形式化陈述：isOrthogonal_reflection (hSB : LinearMap.IsSymm B) : B.IsOrthogonal (Modul
e.reflection (coroot_apply_self B hx))
参数：hSB : LinearMap.IsSymm B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LinearMap.IsReflective.coroot_apply_self`：coroot_apply_self : coroot B h
x x = 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Module.reflection_apply`：reflection_apply (h : f x = 2) : reflection h y
 = y - (f y) • x
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `IsRegular.left`：∀ {R : Type u_1} [inst : Mul R] {c : R}, IsRegular c → I
sLeftRegular c
· 使用定理 `LinearMap.IsReflective.regular`：∀ {R : Type u_1} {M : Type u_2} [inst : 
CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {B : M →ₗ[R
] M →ₗ[R] R} {x : M}…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用引理 `LinearMap.IsReflective.apply_self_mul_coroot_apply`：apply_self_mul_coroo
t_apply {y : M} : B x x * coroot B hx y = 2 * B x y
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 55 条，此处仅展示前 30 条）
-/
lemma isOrthogonal_reflection (hSB : LinearMap.IsSymm B) :
    B.IsOrthogonal (Module.reflection (coroot_apply_self B hx)) := by
  intro y z
  simp only [reflection_apply, map_sub, map_smul, sub_apply,
    smul_apply, smul_eq_mul]
  refine hx.1.1 ?_
  simp only [mul_sub, ← mul_assoc, apply_self_mul_coroot_apply]
  rw [sub_eq_iff_eq_add, ← hSB.eq x y, RingHom.id_apply, mul_assoc _ _ (B x x), mul_comm _ (B x x),
    apply_self_mul_coroot_apply]
  ring
/-
**LinearMap.IsReflective.reflective_reflection** 是 Mathlib 中的一个引理，位于命名空间 `Linear
Map.IsReflective`。
形式化陈述：reflective_reflection (hSB : LinearMap.IsSymm B) {y : M} (hx : IsReflectiv
e B x) (hy : IsReflective B y) : IsReflective B (Module.reflection (coroot_apply
_self B hx) y)
参数：hSB : LinearMap.IsSymm B；hx : IsReflective B x；hy : IsReflective B y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LinearMap.IsReflective.coroot_apply_self`：coroot_apply_self : coroot B h
x x = 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.IsReflective.isOrthogonal_reflection`：isOrthogonal_reflection 
(hSB : LinearMap.IsSymm B) : B.IsOrthogonal (Module.reflection (coroot_apply_sel
f B hx))
· 使用定理 `LinearMap.IsReflective.regular`：∀ {R : Type u_1} {M : Type u_2} [inst : 
CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {B : M →ₗ[R
] M →ₗ[R] R} {x : M}…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsReflective.dvd_two_mul`：∀ {R : Type u_1} {M : Type u_2} [ins
t : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {B : M 
→ₗ[R] M →ₗ[R] R} {x : M}…
-/
lemma reflective_reflection (hSB : LinearMap.IsSymm B) {y : M}
    (hx : IsReflective B x) (hy : IsReflective B y) :
    IsReflective B (Module.reflection (coroot_apply_self B hx) y) := by
  constructor
  · rw [isOrthogonal_reflection B hx hSB]
    exact hy.1
  · intro z
    have hz : Module.reflection (coroot_apply_self B hx)
        (Module.reflection (coroot_apply_self B hx) z) = z := by
      exact (LinearEquiv.eq_symm_apply (Module.reflection (coroot_apply_self B hx))).mp rfl
    rw [← hz, isOrthogonal_reflection B hx hSB,
      isOrthogonal_reflection B hx hSB]
    exact hy.2 _

end IsReflective

end LinearMap

namespace RootPairing

open LinearMap IsReflective

set_option backward.isDefEq.respectTransparency false in
/-- The root pairing given by all reflective vectors for a bilinear form. -/
/-
**RootPairing.ofBilinear** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：ofBilinear [IsReflexive R M] (B : M ->ₗ[R] M ->ₗ[R] R) (hNB : LinearMap.No
ndegenerate B) (hSB : LinearMap.IsSymm B) (h2 : IsRegular (2 : R)) : RootPairing
 {x : M | IsReflective B x} R M (Dual R M) where toLinearMap
参数：B : M ->ₗ[R] M ->ₗ[R] R；hNB : LinearMap.Nondegenerate B；hSB : LinearMap.IsSym
m B；h2 : IsRegular (2 : R)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPerfPair.dualEval`：∀ {R : Type u_1} {M : Type u_3} [inst : A
ddCommGroup M] [inst_1 : CommRing R] [inst_2 : _root_.Module R M]   [Module.IsRe
flexive R M], (Modu…

--- 原说明 ---
The root pairing given by all reflective vectors for a bilinear form.
-/
def ofBilinear [IsReflexive R M] (B : M →ₗ[R] M →ₗ[R] R) (hNB : LinearMap.Nondegenerate B)
    (hSB : LinearMap.IsSymm B) (h2 : IsRegular (2 : R)) :
    RootPairing {x : M | IsReflective B x} R M (Dual R M) where
  toLinearMap := Dual.eval R M
  root := Embedding.subtype fun x ↦ IsReflective B x
  coroot :=
    { toFun := fun x => IsReflective.coroot B x.2
      inj' := by
        intro x y hxy
        simp only [mem_ofPred_eq] at hxy -- x* = y*
        have h1 : ∀ z, IsReflective.coroot B x.2 z = IsReflective.coroot B y.2 z :=
          fun z => congrFun (congrArg DFunLike.coe hxy) z
        have h2x : ∀ z, B x x * IsReflective.coroot B x.2 z =
            B x x * IsReflective.coroot B y.2 z :=
          fun z => congrArg (HMul.hMul ((B x) x)) (h1 z)
        have h2y : ∀ z, B y y * IsReflective.coroot B x.2 z =
            B y y * IsReflective.coroot B y.2 z :=
          fun z => congrArg (HMul.hMul ((B y) y)) (h1 z)
        simp_rw [apply_self_mul_coroot_apply B x.2] at h2x -- 2(x,z) = (x,x)y*(z)
        simp_rw [apply_self_mul_coroot_apply B y.2] at h2y -- (y,y)x*(z) = 2(y,z)
        have h2xy : B x x = B y y := by
          refine h2.1 ?_
          dsimp only
          specialize h2x y
          rw [coroot_apply_self] at h2x
          specialize h2y x
          rw [coroot_apply_self] at h2y
          rw [mul_comm, ← h2x, ← hSB.eq, RingHom.id_apply, ← h2y, mul_comm]
        rw [Subtype.ext_iff, ← sub_eq_zero]
        refine hNB.1 _ (fun z => ?_)
        rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
        refine h2.1 ?_
        dsimp only
        rw [h2x z, ← h2y z, hxy, h2xy] }
  root_coroot_two x := coroot_apply_self B x.2
  reflectionPerm x :=
    { toFun := fun y => ⟨(Module.reflection (coroot_apply_self B x.2) y),
        reflective_reflection B hSB x.2 y.2⟩
      invFun := fun y => ⟨(Module.reflection (coroot_apply_self B x.2) y),
        reflective_reflection B hSB x.2 y.2⟩
      left_inv := by
        intro y
        simp [involutive_reflection (coroot_apply_self B x.2) y]
      right_inv := by
        intro y
        simp [involutive_reflection (coroot_apply_self B x.2) y] }
  reflectionPerm_root := by
    simp [coe_ofPred, Module.reflection_apply]
  reflectionPerm_coroot x y := by
    simp only [coe_ofPred, mem_ofPred_eq, Embedding.coeFn_mk, Embedding.subtype_apply,
      Dual.eval_apply, Equiv.coe_fn_mk]
    ext z
    simp only [sub_apply, smul_apply, smul_eq_mul]
    refine y.2.1.1 ?_
    simp only [mem_ofPred_eq, mul_sub, apply_self_mul_coroot_apply B y.2, ← mul_assoc]
    rw [← isOrthogonal_reflection B x.2 hSB y y, apply_self_mul_coroot_apply, ← hSB.eq z,
      ← hSB.eq z, RingHom.id_apply, RingHom.id_apply, Module.reflection_apply, map_sub,
      mul_sub, sub_eq_sub_iff_comm, sub_left_inj]
    refine x.2.1.1 ?_
    simp only [mem_ofPred_eq, map_smul, smul_eq_mul]
    rw [← mul_assoc _ _ (B z x), ← mul_assoc _ _ (B z x), mul_left_comm,
      apply_self_mul_coroot_apply B x.2, mul_left_comm (B x x), apply_self_mul_coroot_apply B x.2,
      ← hSB.eq x y, RingHom.id_apply, ← hSB.eq x z, RingHom.id_apply]
    ring

end RootPairing

