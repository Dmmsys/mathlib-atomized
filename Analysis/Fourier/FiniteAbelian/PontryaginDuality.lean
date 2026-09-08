/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.DirectSum.AddChar
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Algebra.Field.ModEq

/-!
# Pontryagin duality for finite abelian groups

This file proves the Pontryagin duality in case of finite abelian groups. This states that any
finite abelian group is canonically isomorphic to its double dual (the space of complex-valued
characters of its space of complex-valued characters).

We first prove it for `ZMod n` and then extend to all finite abelian groups using the
Structure Theorem.

## TODO

Reuse the work done in `Mathlib/GroupTheory/FiniteAbelian/Duality.lean`. This requires to write some
more glue.
-/

@[expose] public section

noncomputable section

open Circle Finset Function Module Multiplicative
open Fintype (card)
open Real hiding exp
open scoped BigOperators DirectSum

variable {α : Type*} [AddCommGroup α] {n : ℕ} {a b : α}

namespace AddChar
variable (n : ℕ) [NeZero n]

/-- Indexing of the complex characters of `ZMod n`. `AddChar.zmod n x` is the character sending `y`
to `e ^ (2 * π * i * x * y / n)`. -/
/-
**AddChar.zmod** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：zmod (x : ZMod n) : AddChar (ZMod n) Circle
参数：x : ZMod n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Indexing of the complex characters of `ZMod n`. `AddChar.zmod n x` is the charac
ter sending `y`
to `e ^ (2 * π * i * x * y / n)`.
-/
def zmod (x : ZMod n) : AddChar (ZMod n) Circle :=
  AddChar.compAddMonoidHom ⟨AddCircle.toCircle, AddCircle.toCircle_zero, AddCircle.toCircle_add⟩ <|
    ZMod.toAddCircle.comp <| .mulLeft x
/-
**AddChar.zmod_intCast** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ (n : ℕ) [inst : NeZero n] (x y : ℤ), (AddChar.zmod n ↑x) ↑y = Circle.exp
 (2 * Real.pi * (↑x * ↑y / ↑n))
参数：n : ℕ；x y : ℤ；AddChar.zmod n ↑x；2 * Real.pi * (↑x * ↑y / ↑n)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用引理 `ZMod.toAddCircle_intCast`：toAddCircle_intCast (j : Int) : toAddCircle (j
 : ZMod N) = ↑(j / N : Real)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddChar.coe_mk`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [in
st_1 : Monoid M] (f : A → M) (map_zero_eq_one' : f 0 = 1)   (map_add_eq_mul' : ∀
 (a …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma zmod_intCast (x y : ℤ) : zmod n x y = exp (2 * π * (x * y / n)) := by
  simp [zmod, ← Int.cast_mul x y, -Int.cast_mul, ZMod.toAddCircle_intCast,
    AddCircle.toCircle_apply_mk]
/-
**AddChar.zmod_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ (n : ℕ) [inst : NeZero n], AddChar.zmod n 0 = 1
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma zmod_zero : zmod n 0 = 1 :=
  DFunLike.ext _ _ <| by simp [zmod]

variable {n}
/-
**AddChar.zmod_add** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {n : ℕ} [inst : NeZero n] (x y : ZMod n), AddChar.zmod n (x + y) = AddCh
ar.zmod n x * AddChar.zmod n y
参数：x y : ZMod n；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `AddChar.map_add_eq_mul`：map_add_eq_mul (ψ : AddChar A M) (x y : A) : ψ (
x + y) = ψ x * ψ y
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AddChar.coe_mk`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMonoid A] [in
st_1 : Monoid M] (f : A → M) (map_zero_eq_one' : f 0 = 1)   (map_add_eq_mul' : ∀
 (a …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma zmod_add : ∀ x y : ZMod n, zmod n (x + y) = zmod n x * zmod n y := by
  simp [DFunLike.ext_iff, zmod, add_mul, map_add_eq_mul]
/-
**AddChar.zmod_injective** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：zmod_injective : Injective (zmod n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `ZMod.intCast_surjective`：intCast_surjective : Function.Surjective ((↑) :
 Int -> ZMod n)
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `CharP.intCast_eq_intCast`：intCast_eq_intCast : (a : R) = b ↔ a ≡ b [ZMOD
 p]
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddChar.zmod_intCast`：∀ (n : ℕ) [inst : NeZero n] (x y : ℤ), (AddChar.zm
od n ↑x) ↑y = Circle.exp (2 * Real.pi * (↑x * ↑y / ↑n))
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
lemma zmod_injective : Injective (zmod n) := by
  simp_rw [Injective, ZMod.intCast_surjective.forall]
  rintro x y h
  have hn : (n : ℝ) ≠ 0 := NeZero.ne _
  simpa [pi_ne_zero, exp_inj, hn, CharP.intCast_eq_intCast (ZMod n) n] using
    (zmod_intCast ..).symm.trans <| (DFunLike.congr_fun h ((1 : ℤ) : ZMod n)).trans <|
      zmod_intCast ..
/-
**AddChar.zmod_inj** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {n : ℕ} [inst : NeZero n] {x y : ZMod n}, AddChar.zmod n x = AddChar.zmo
d n y ↔ x = y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `AddChar.zmod_injective`：zmod_injective : Injective (zmod n)
-/
@[simp] lemma zmod_inj {x y : ZMod n} : zmod n x = zmod n y ↔ x = y := zmod_injective.eq_iff

/-- `AddChar.zmod` bundled as an `AddChar`. -/
/-
**AddChar.zmodHom** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：zmodHom : AddChar (ZMod n) (AddChar (ZMod n) Circle) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddChar.zmod` bundled as an `AddChar`.
-/
def zmodHom : AddChar (ZMod n) (AddChar (ZMod n) Circle) where
  toFun := zmod n
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp

/-- Character on a product of `ZMod`s given by `x ↦ ∏ i, e ^ (2 * π * I * x i * y / n)`. -/
/-
**AddChar.mkZModAux** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Character on a product of `ZMod`s given by `x ↦ ∏ i, e ^ (2 * π * I * x i * y / 
n)`.
-/
private def mkZModAux {ι : Type*} [DecidableEq ι] (n : ι → ℕ) [∀ i, NeZero (n i)]
    (u : ∀ i, ZMod (n i)) : AddChar (⨁ i, ZMod (n i)) Circle :=
  AddChar.directSum fun i ↦ zmod (n i) (u i)
/-
**AddChar.mkZModAux_injective** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mkZModAux_injective {ι : Type*} [DecidableEq ι] {n : ι → ℕ} [∀ i, NeZero (n i)] :
    Injective (mkZModAux n) :=
  AddChar.directSum_injective.comp fun f g h ↦ by simpa [funext_iff] using h

set_option backward.isDefEq.respectTransparency false in
/-- The circle-valued characters of a finite abelian group are the same as its complex-valued
characters. -/
/-
**AddChar.circleEquivComplex** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：circleEquivComplex [Finite α] : AddChar α Circle ≃+ AddChar α Complex wher
e toFun ψ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The circle-valued characters of a finite abelian group are the same as its compl
ex-valued
characters.
-/
def circleEquivComplex [Finite α] : AddChar α Circle ≃+ AddChar α ℂ where
  toFun ψ := toMonoidHomEquiv.symm <| coeHom.comp ψ.toMonoidHom
  invFun ψ :=
    { toFun := fun a ↦ (⟨ψ a, mem_sphere_zero_iff_norm.2 <| ψ.norm_apply _⟩ : Circle)
      map_zero_eq_one' := by simp [Circle]
      map_add_eq_mul' := fun a b ↦ by ext : 1; simp [map_add_eq_mul] }
  left_inv ψ := by ext : 1; simp
  right_inv ψ := by ext : 1; simp
  map_add' ψ χ := rfl
/-
**AddChar.card_eq** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Fintype α], Fintype.car
d (AddChar α ℂ) = Fintype.card α
参数：AddChar α ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `AddCommGroup.equiv_directSum_zmod_of_finite'`：equiv_directSum_zmod_of_fi
nite' (G : Type*) [AddCommGroup G] [Finite G] : exists (ι : Type) (_ : Fintype ι
) (n : ι -> Nat), (forall i, 1 < n…
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `AddChar.compAddMonoidHom_injective_left`：compAddMonoidHom_injective_left
 (f : A ->+ B) (hf : Surjective f) : Injective fun ψ : AddChar B M => ψ.compAddM
onoidHom f
· 使用定理 `AddEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [ins
t_1 : Add N] (e : M ≃+ N), Function.Surjective ⇑e
· 使用定理 `_private.Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality.0.AddC
har.mkZModAux_injective`：∀ {ι : Type u_2} [inst : DecidableEq ι] {n : ι → ℕ} [in
st_1 : ∀ (i : ι), NeZero (n i)],   Function.Injective (AddChar.mkZModAux✝ n)
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `AddChar.card_addChar_le`：∀ (G : Type u_1) (R : Type u_3) [inst : AddComm
Group G] [inst_1 : RCLike R] [inst_2 : Fintype G],   Fintype.card (AddChar G R) 
≤ Fintype.car…
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
-/
@[simp] lemma card_eq [Fintype α] : card (AddChar α ℂ) = card α := by
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' α
  classical
  have hn' i : NeZero (n i) := by have := hn i; exact ⟨by positivity⟩
  let f : α → AddChar α ℂ := fun a ↦ coeHom.compAddChar ((mkZModAux n <| e a).compAddMonoidHom e)
  have hf : Injective f := circleEquivComplex.injective.comp
    ((compAddMonoidHom_injective_left _ e.surjective).comp <| mkZModAux_injective.comp <|
      DFunLike.coe_injective.comp <| e.injective.comp Additive.ofMul.injective)
  exact (card_addChar_le _ _).antisymm (Fintype.card_le_of_injective _ hf)

/-- `ZMod n` is (noncanonically) isomorphic to its group of characters. -/
/-
**AddChar.zmodAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：zmodAddEquiv : ZMod n ≃+ AddChar (ZMod n) Complex
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ZMod n` is (noncanonically) isomorphic to its group of characters.
-/
def zmodAddEquiv : ZMod n ≃+ AddChar (ZMod n) ℂ := by
  refine AddEquiv.ofBijective
    (circleEquivComplex.toAddMonoidHom.comp <| AddChar.toAddMonoidHom zmodHom) ?_
  rw [Fintype.bijective_iff_injective_and_card, card_eq]
  exact ⟨circleEquivComplex.injective.comp zmod_injective, rfl⟩
/-
**AddChar.zmodAddEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {n : ℕ} [inst : NeZero n] (x : ZMod n), AddChar.zmodAddEquiv x = AddChar
.circleEquivComplex (AddChar.zmod n x)
参数：x : ZMod n；AddChar.zmod n x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma zmodAddEquiv_apply (x : ZMod n) :
    zmodAddEquiv x = circleEquivComplex (zmod n x) := rfl

section Finite
variable (α) [Finite α]

/-- Complex-valued characters of a finite abelian group `α` form a basis of `α → ℂ`. -/
/-
**AddChar.complexBasis** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：complexBasis : Basis (AddChar α Complex) Complex (α -> Complex)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.linearIndependent`：∀ (G : Type u_1) (R : Type u_3) [inst : AddCo
mmGroup G] [inst_1 : RCLike R] [Finite G], LinearIndependent R DFunLike.coe

--- 原说明 ---
Complex-valued characters of a finite abelian group `α` form a basis of `α → ℂ`.
-/
def complexBasis : Basis (AddChar α ℂ) ℂ (α → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (AddChar.linearIndependent _ _) <| by
    cases nonempty_fintype α; rw [card_eq, Module.finrank_fintype_fun_eq_card]

@[simp, norm_cast]
/-
**AddChar.coe_complexBasis** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：coe_complexBasis : ⇑(complexBasis α) = ((⇑) : AddChar α Complex -> α -> Co
mplex)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.linearIndependent`：∀ (G : Type u_1) (R : Type u_3) [inst : AddCo
mmGroup G] [inst_1 : RCLike R] [Finite G], LinearIndependent R DFunLike.coe
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddChar.complexBasis.eq_1`：∀ (α : Type u_1) [inst : AddCommGroup α] [ins
t_1 : Finite α],   AddChar.complexBasis α = basisOfLinearIndependentOfCardEqFinr
ank ⋯ ⋯
· 使用定理 `coe_basisOfLinearIndependentOfCardEqFinrank`：coe_basisOfLinearIndependen
tOfCardEqFinrank [Nonempty ι] {b : ι -> V} (lin_ind : LinearIndependent K b) (ca
rd_eq : Fintype.card ι = finrank …
-/
lemma coe_complexBasis : ⇑(complexBasis α) = ((⇑) : AddChar α ℂ → α → ℂ) := by
  rw [complexBasis, coe_basisOfLinearIndependentOfCardEqFinrank]

variable {α}

@[simp]
/-
**AddChar.complexBasis_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：complexBasis_apply (ψ : AddChar α Complex) : complexBasis α ψ = ψ
参数：ψ : AddChar α Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.coe_complexBasis`：coe_complexBasis : ⇑(complexBasis α) = ((⇑) : 
AddChar α Complex -> α -> Complex)
-/
lemma complexBasis_apply (ψ : AddChar α ℂ) : complexBasis α ψ = ψ := by rw [coe_complexBasis]
/-
**AddChar.exists_apply_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：exists_apply_ne_zero : (exists ψ : AddChar α Complex, ψ a != 1) ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.sum_repr`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_6} [i
nst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [ins
t_3 : Finty…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `AddChar.complexBasis_apply`：complexBasis_apply (ψ : AddChar α Complex) :
 complexBasis α ψ = ψ
· 使用定理 `Fintype.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [i
nst : Fintype ι] [inst_1 : (a : α) → AddCommMonoid (M a)] (a : α)   (g : ι → (a 
: α) → …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma exists_apply_ne_zero : (∃ ψ : AddChar α ℂ, ψ a ≠ 1) ↔ a ≠ 0 := by
  refine ⟨?_, fun ha ↦ ?_⟩
  · rintro ⟨ψ, hψ⟩ rfl
    exact hψ ψ.map_zero_eq_one
  classical
  by_contra! h
  let f : α → ℂ := fun b ↦ if a = b then 1 else 0
  have h₀ := congr_fun ((complexBasis α).sum_repr f) 0
  have h₁ := congr_fun ((complexBasis α).sum_repr f) a
  simp only [complexBasis_apply, Fintype.sum_apply, Pi.smul_apply, h, smul_eq_mul, mul_one,
    map_zero_eq_one, if_pos rfl, if_neg ha, f] at h₀ h₁
  exact one_ne_zero (h₁.symm.trans h₀)
/-
**AddChar.forall_apply_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：forall_apply_eq_zero : (forall ψ : AddChar α Complex, ψ a = 1) ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `AddChar.exists_apply_ne_zero`：exists_apply_ne_zero : (exists ψ : AddChar
 α Complex, ψ a != 1) ↔ a != 0
-/
lemma forall_apply_eq_zero : (∀ ψ : AddChar α ℂ, ψ a = 1) ↔ a = 0 := by
  simpa using exists_apply_ne_zero.not
/-
**AddChar.doubleDualEmb_injective** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：doubleDualEmb_injective : Injective (doubleDualEmb : α -> AddChar (AddChar
 α Complex) Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AddMonoidHom.ker_eq_bot_iff`：∀ {G : Type u_1} [inst : AddGroup G] {M : T
ype u_7} [inst_1 : AddZeroClass M] (f : G →+ M),   f.ker = ⊥ ↔ Function.Injectiv
e ⇑f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `AddChar.forall_apply_eq_zero`：forall_apply_eq_zero : (forall ψ : AddChar
 α Complex, ψ a = 1) ↔ a = 0
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
lemma doubleDualEmb_injective : Injective (doubleDualEmb : α → AddChar (AddChar α ℂ) ℂ) :=
  doubleDualEmb.ker_eq_bot_iff.1 <| eq_bot_iff.2 fun a ha ↦
    forall_apply_eq_zero.1 fun ψ ↦ by simpa using! DFunLike.congr_fun ha (Additive.ofMul ψ)
/-
**AddChar.doubleDualEmb_bijective** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：doubleDualEmb_bijective : Bijective (doubleDualEmb : α -> AddChar (AddChar
 α Complex) Complex)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Fintype.bijective_iff_injective_and_card`：bijective_iff_injective_and_ca
rd (f : α -> β) : Bijective f ↔ Injective f ∧ card α = card β
· 使用引理 `AddChar.doubleDualEmb_injective`：doubleDualEmb_injective : Injective (do
ubleDualEmb : α -> AddChar (AddChar α Complex) Complex)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddChar.card_eq`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Fint
ype α], Fintype.card (AddChar α ℂ) = Fintype.card α
-/
lemma doubleDualEmb_bijective : Bijective (doubleDualEmb : α → AddChar (AddChar α ℂ) ℂ) := by
  cases nonempty_fintype α
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨doubleDualEmb_injective, card_eq.symm.trans card_eq.symm⟩

@[simp]
/-
**AddChar.doubleDualEmb_inj** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：doubleDualEmb_inj : (doubleDualEmb a : AddChar (AddChar α Complex) Complex
) = doubleDualEmb b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `AddChar.doubleDualEmb_injective`：doubleDualEmb_injective : Injective (do
ubleDualEmb : α -> AddChar (AddChar α Complex) Complex)
-/
lemma doubleDualEmb_inj : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) = doubleDualEmb b ↔ a = b :=
  doubleDualEmb_injective.eq_iff
/-
**AddChar.doubleDualEmb_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddChar`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommGroup α] {a : α} [Finite α], AddChar.doubl
eDualEmb a = 0 ↔ a = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用引理 `AddChar.doubleDualEmb_inj`：doubleDualEmb_inj : (doubleDualEmb a : AddCha
r (AddChar α Complex) Complex) = doubleDualEmb b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma doubleDualEmb_eq_zero : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) = 0 ↔ a = 0 := by
  rw [← map_zero doubleDualEmb, doubleDualEmb_inj]
/-
**AddChar.doubleDualEmb_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：doubleDualEmb_ne_zero : (doubleDualEmb a : AddChar (AddChar α Complex) Com
plex) != 0 ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `AddChar.doubleDualEmb_eq_zero`：∀ {α : Type u_1} [inst : AddCommGroup α] 
{a : α} [Finite α], AddChar.doubleDualEmb a = 0 ↔ a = 0
-/
lemma doubleDualEmb_ne_zero : (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ) ≠ 0 ↔ a ≠ 0 :=
  doubleDualEmb_eq_zero.not

/-- The double dual isomorphism of a finite abelian group. -/
/-
**AddChar.doubleDualEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：doubleDualEquiv : α ≃+ AddChar (AddChar α Complex) Complex
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AddChar.doubleDualEmb_bijective`：doubleDualEmb_bijective : Bijective (do
ubleDualEmb : α -> AddChar (AddChar α Complex) Complex)

--- 原说明 ---
The double dual isomorphism of a finite abelian group.
-/
def doubleDualEquiv : α ≃+ AddChar (AddChar α ℂ) ℂ := .ofBijective _ doubleDualEmb_bijective

@[simp]
/-
**AddChar.coe_doubleDualEquiv** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：coe_doubleDualEquiv : ⇑(doubleDualEquiv : α ≃+ AddChar (AddChar α Complex)
 Complex) = doubleDualEmb
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_doubleDualEquiv : ⇑(doubleDualEquiv : α ≃+ AddChar (AddChar α ℂ) ℂ) = doubleDualEmb := rfl
/-
**AddChar.doubleDualEmb_doubleDualEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ad
dChar`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Finite α] (a : AddChar 
(AddChar α ℂ) ℂ),   AddChar.doubleDualEmb (AddChar.doubleDualEquiv.symm a) = a
参数：a : AddChar (AddChar α ℂ) ℂ；AddChar.doubleDualEquiv.symm a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
-/
@[simp] lemma doubleDualEmb_doubleDualEquiv_symm_apply (a : AddChar (AddChar α ℂ) ℂ) :
    doubleDualEmb (doubleDualEquiv.symm a) = a :=
  doubleDualEquiv.apply_symm_apply _
/-
**AddChar.doubleDualEquiv_symm_doubleDualEmb_apply** 是 Mathlib 中的一个定理，位于命名空间 `Ad
dChar`。
形式化陈述：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Finite α] (a : AddChar 
(AddChar α ℂ) ℂ),   AddChar.doubleDualEquiv.symm (AddChar.doubleDualEmb a) = a
参数：a : AddChar (AddChar α ℂ) ℂ；AddChar.doubleDualEmb a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddEquiv.symm_apply_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (x : M), e.symm (e x) = x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
@[simp] lemma doubleDualEquiv_symm_doubleDualEmb_apply (a : AddChar (AddChar α ℂ) ℂ) :
    doubleDualEquiv.symm (doubleDualEmb a) = a := doubleDualEquiv.symm_apply_apply _

end Finite

/-
**AddChar.sum_apply_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：sum_apply_eq_ite [Fintype α] [DecidableEq α] (a : α) : ∑ ψ : AddChar α Com
plex, ψ a = if a = 0 then (Fintype.card α : Complex) else 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `AddChar.card_eq`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Fint
ype α], Fintype.card (AddChar α ℂ) = Fintype.card α
· 使用引理 `AddChar.sum_eq_ite`：sum_eq_ite (ψ : AddChar A R) [Decidable (ψ = 0)] : ∑
 a, ψ a = if ψ = 0 then ↑(card A) else 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
lemma sum_apply_eq_ite [Fintype α] [DecidableEq α] (a : α) :
    ∑ ψ : AddChar α ℂ, ψ a = if a = 0 then (Fintype.card α : ℂ) else 0 := by
  simpa using sum_eq_ite (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ)
/-
**AddChar.expect_apply_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：expect_apply_eq_ite [Finite α] [DecidableEq α] (a : α) : 𝔼 ψ : AddChar α C
omplex, ψ a = if a = 0 then 1 else 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `AddChar.expect_eq_ite`：expect_eq_ite (ψ : AddChar G R) : 𝔼 a, ψ a = if ψ
 = 0 then 1 else 0
-/
lemma expect_apply_eq_ite [Finite α] [DecidableEq α] (a : α) :
    𝔼 ψ : AddChar α ℂ, ψ a = if a = 0 then 1 else 0 := by
  simpa using expect_eq_ite (doubleDualEmb a : AddChar (AddChar α ℂ) ℂ)
/-
**AddChar.sum_apply_eq_zero_iff_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：sum_apply_eq_zero_iff_ne_zero [Finite α] : ∑ ψ : AddChar α Complex, ψ a = 
0 ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `AddChar.sum_apply_eq_ite`：sum_apply_eq_ite [Fintype α] [DecidableEq α] (
a : α) : ∑ ψ : AddChar α Complex, ψ a = if a = 0 then (Fintype.card α : Complex)
 else 0
· 使用定理 `Ne.ite_eq_right_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a
 b : α}, a ≠ b → ((if P then a else b) = b ↔ ¬P)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `Fintype.card_ne_zero`：card_ne_zero [Nonempty α] : card α != 0
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma sum_apply_eq_zero_iff_ne_zero [Finite α] : ∑ ψ : AddChar α ℂ, ψ a = 0 ↔ a ≠ 0 := by
  classical
  cases nonempty_fintype α
  rw [sum_apply_eq_ite, Ne.ite_eq_right_iff]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero
/-
**AddChar.sum_apply_ne_zero_iff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：sum_apply_ne_zero_iff_eq_zero [Finite α] : ∑ ψ : AddChar α Complex, ψ a !=
 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `AddChar.sum_apply_eq_zero_iff_ne_zero`：sum_apply_eq_zero_iff_ne_zero [Fi
nite α] : ∑ ψ : AddChar α Complex, ψ a = 0 ↔ a != 0
-/
lemma sum_apply_ne_zero_iff_eq_zero [Finite α] : ∑ ψ : AddChar α ℂ, ψ a ≠ 0 ↔ a = 0 :=
  sum_apply_eq_zero_iff_ne_zero.not_left
/-
**AddChar.expect_apply_eq_zero_iff_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：expect_apply_eq_zero_iff_ne_zero [Finite α] : 𝔼 ψ : AddChar α Complex, ψ a
 = 0 ↔ a != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AddChar.expect_apply_eq_ite`：expect_apply_eq_ite [Finite α] [DecidableEq
 α] (a : α) : 𝔼 ψ : AddChar α Complex, ψ a = if a = 0 then 1 else 0
· 使用定理 `Ne.ite_eq_right_iff`：∀ {α : Sort u_1} {P : Prop} [inst : Decidable P] {a
 b : α}, a ≠ b → ((if P then a else b) = b ↔ ¬P)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma expect_apply_eq_zero_iff_ne_zero [Finite α] : 𝔼 ψ : AddChar α ℂ, ψ a = 0 ↔ a ≠ 0 := by
  classical
  cases nonempty_fintype α
  rw [expect_apply_eq_ite, one_ne_zero.ite_eq_right_iff]
/-
**AddChar.expect_apply_ne_zero_iff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：expect_apply_ne_zero_iff_eq_zero [Finite α] : 𝔼 ψ : AddChar α Complex, ψ a
 != 0 ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_left`：Iff.not_left (h : a ↔ ¬b) : ¬a ↔ b
· 使用引理 `AddChar.expect_apply_eq_zero_iff_ne_zero`：expect_apply_eq_zero_iff_ne_ze
ro [Finite α] : 𝔼 ψ : AddChar α Complex, ψ a = 0 ↔ a != 0
-/
lemma expect_apply_ne_zero_iff_eq_zero [Finite α] : 𝔼 ψ : AddChar α ℂ, ψ a ≠ 0 ↔ a = 0 :=
  expect_apply_eq_zero_iff_ne_zero.not_left

end AddChar

