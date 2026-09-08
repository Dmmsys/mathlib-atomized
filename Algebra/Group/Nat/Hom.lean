/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Tactic.Spread

/-!
# Extensionality of monoid homs from `ℕ`
-/

@[expose] public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Additive Multiplicative

variable {M : Type*}

section AddMonoidHomClass

variable {A B F : Type*} [FunLike F ℕ A]

/-
**ext_nat'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ext_nat' [AddZeroClass A] [AddMonoidHomClass F Nat A] (f g : F) (h : f 1 =
 g 1) : f = g
参数：f g : F；h : f 1 = g 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
-/
lemma ext_nat' [AddZeroClass A] [AddMonoidHomClass F ℕ A] (f g : F) (h : f 1 = g 1) : f = g :=
  DFunLike.ext f g <| by
    intro n
    induction n with
    | zero => simp_rw [map_zero f, map_zero g]
    | succ n ihn =>
      simp [h, ihn]

@[ext]
/-
**AddMonoidHom.ext_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidHom.ext_nat [AddZeroClass A] {f g : Nat ->+ A} : f 1 = g 1 -> f =
 g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ext_nat'`：ext_nat' [AddZeroClass A] [AddMonoidHomClass F Nat A] (f g : F
) (h : f 1 = g 1) : f = g
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma AddMonoidHom.ext_nat [AddZeroClass A] {f g : ℕ →+ A} : f 1 = g 1 → f = g :=
  ext_nat' f g

end AddMonoidHomClass

section AddMonoid
variable [AddMonoid M]

variable (M) in
/-- Additive homomorphisms from `ℕ` are defined by the image of `1`. -/
/-
**multiplesHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：multiplesHom : M ≃ (Nat ->+ M) where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `add_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (m n : ℕ), (m +
 n) • a = m • a + n • a
· 使用定理 `one_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 1 • a = a

--- 原说明 ---
Additive homomorphisms from `ℕ` are defined by the image of `1`.
-/
def multiplesHom : M ≃ (ℕ →+ M) where
  toFun x :=
  { toFun := fun n ↦ n • x
    map_zero' := zero_nsmul x
    map_add' := fun _ _ ↦ add_nsmul _ _ _ }
  invFun f := f 1
  left_inv := one_nsmul
  right_inv f := AddMonoidHom.ext_nat <| one_nsmul (f 1)
/-
**multiplesHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : AddMonoid M] (x : M) (n : ℕ), ((multiplesHom M) x
) n = n • x
参数：x : M；n : ℕ；(multiplesHom M) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma multiplesHom_apply (x : M) (n : ℕ) : multiplesHom M x n = n • x := rfl
/-
**multiplesHom_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : AddMonoid M] (f : ℕ →+ M), (multiplesHom M).symm 
f = f 1
参数：f : ℕ →+ M；multiplesHom M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma multiplesHom_symm_apply (f : ℕ →+ M) : (multiplesHom M).symm f = f 1 := rfl
/-
**AddMonoidHom.apply_nat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddMonoidHom.apply_nat (f : Nat ->+ M) (n : Nat) : f n = n • f 1
参数：f : Nat ->+ M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `multiplesHom_symm_apply`：∀ {M : Type u_1} [inst : AddMonoid M] (f : ℕ →+
 M), (multiplesHom M).symm f = f 1
· 使用定理 `multiplesHom_apply`：∀ {M : Type u_1} [inst : AddMonoid M] (x : M) (n : ℕ
), ((multiplesHom M) x) n = n • x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma AddMonoidHom.apply_nat (f : ℕ →+ M) (n : ℕ) : f n = n • f 1 := by
  rw [← multiplesHom_symm_apply, ← multiplesHom_apply, Equiv.apply_symm_apply]

end AddMonoid

section Monoid
variable [Monoid M]

variable (M) in
/-- Monoid homomorphisms from `Multiplicative ℕ` are defined by the image
of `Multiplicative.ofAdd 1`. -/
/-
**powersHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：powersHom : M ≃ (Multiplicative Nat ->* M)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Monoid homomorphisms from `Multiplicative ℕ` are defined by the image
of `Multiplicative.ofAdd 1`.
-/
def powersHom : M ≃ (Multiplicative ℕ →* M) :=
  Additive.ofMul.trans <| (multiplesHom _).trans <| AddMonoidHom.toMultiplicativeLeft
/-
**powersHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] (x : M) (n : Multiplicative ℕ), ((power
sHom M) x) n = x ^ Multiplicative.toAdd n
参数：x : M；n : Multiplicative ℕ；(powersHom M) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma powersHom_apply (x : M) (n : Multiplicative ℕ) :
    powersHom M x n = x ^ n.toAdd := rfl
/-
**powersHom_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : Monoid M] (f : Multiplicative ℕ →* M), (powersHom
 M).symm f = f (Multiplicative.ofAdd 1)
参数：f : Multiplicative ℕ →* M；powersHom M；Multiplicative.ofAdd 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
@[simp] lemma powersHom_symm_apply (f : Multiplicative ℕ →* M) :
    (powersHom M).symm f = f (Multiplicative.ofAdd 1) := rfl
/-
**MonoidHom.apply_mnat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.apply_mnat (f : Multiplicative Nat ->* M) (n : Multiplicative Na
t) : f n = f (Multiplicative.ofAdd 1) ^ n.toAdd
参数：f : Multiplicative Nat ->* M；n : Multiplicative Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `powersHom_symm_apply`：∀ {M : Type u_1} [inst : Monoid M] (f : Multiplica
tive ℕ →* M), (powersHom M).symm f = f (Multiplicative.ofAdd 1)
· 使用定理 `powersHom_apply`：∀ {M : Type u_1} [inst : Monoid M] (x : M) (n : Multipl
icative ℕ), ((powersHom M) x) n = x ^ Multiplicative.toAdd n
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma MonoidHom.apply_mnat (f : Multiplicative ℕ →* M) (n : Multiplicative ℕ) :
    f n = f (Multiplicative.ofAdd 1) ^ n.toAdd := by
  rw [← powersHom_symm_apply, ← powersHom_apply, Equiv.apply_symm_apply]

@[ext]
/-
**MonoidHom.ext_mnat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.ext_mnat ⦃f g : Multiplicative Nat ->* M⦄ (h : f (Multiplicative
.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidHom.apply_mnat`：MonoidHom.apply_mnat (f : Multiplicative Nat ->* M
) (n : Multiplicative Nat) : f n = f (Multiplicative.ofAdd 1) ^ n.toAdd
-/
lemma MonoidHom.ext_mnat ⦃f g : Multiplicative ℕ →* M⦄
    (h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g :=
  MonoidHom.ext fun n ↦ by rw [f.apply_mnat, g.apply_mnat, h]

end Monoid

section AddCommMonoid
variable [AddCommMonoid M]

variable (M) in
/-- If `M` is commutative, `multiplesHom` is an additive equivalence. -/
/-
**multiplesAddHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：multiplesAddHom : M ≃+ (Nat ->+ M) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is commutative, `multiplesHom` is an additive equivalence.
-/
def multiplesAddHom : M ≃+ (ℕ →+ M) where
  __ := multiplesHom M
  map_add' a b := AddMonoidHom.ext fun n ↦ by simp [nsmul_add]
/-
**multiplesAddHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] (x : M) (n : ℕ), ((multiplesAddH
om M) x) n = n • x
参数：x : M；n : ℕ；(multiplesAddHom M) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma multiplesAddHom_apply (x : M) (n : ℕ) : multiplesAddHom M x n = n • x := rfl
/-
**multiplesAddHom_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {M : Type u_1} [inst : AddCommMonoid M] (f : ℕ →+ M), (multiplesAddHom M
).symm f = f 1
参数：f : ℕ →+ M；multiplesAddHom M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma multiplesAddHom_symm_apply (f : ℕ →+ M) : (multiplesAddHom M).symm f = f 1 := rfl

end AddCommMonoid

section CommMonoid
variable [CommMonoid M]

variable (M) in
/-- If `M` is commutative, `powersHom` is a multiplicative equivalence. -/
/-
**powersMulHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：powersMulHom : M ≃* (Multiplicative Nat ->* M) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is commutative, `powersHom` is a multiplicative equivalence.
-/
def powersMulHom : M ≃* (Multiplicative ℕ →* M) where
  __ := powersHom M
  map_mul' a b := MonoidHom.ext fun n ↦ by simp [mul_pow]

@[simp]
/-
**powersMulHom_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：powersMulHom_apply (x : M) (n : Multiplicative Nat) : powersMulHom M x n =
 x ^ n.toAdd
参数：x : M；n : Multiplicative Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma powersMulHom_apply (x : M) (n : Multiplicative ℕ) : powersMulHom M x n = x ^ n.toAdd := rfl

@[simp]
/-
**powersMulHom_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：powersMulHom_symm_apply (f : Multiplicative Nat ->* M) : (powersMulHom M).
symm f = f (ofAdd 1)
参数：f : Multiplicative Nat ->* M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma powersMulHom_symm_apply (f : Multiplicative ℕ →* M) : (powersMulHom M).symm f = f (ofAdd 1) :=
  rfl

end CommMonoid

