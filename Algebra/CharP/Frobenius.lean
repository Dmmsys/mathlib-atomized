/-
Copyright (c) 2021 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.CharP.Lemmas

/-!
### The Frobenius endomorphism

## Tags

Frobenius endomorphism

## Implementation notes

The definitions of `frobenius` and `iterateFrobenius` ring homomorphisms are in
`Mathlib/Algebra/CharP/Lemmas.lean` as they are needed for some results that in turn are used in
files forbidding to import algebra-related definitions (see `Mathlib/Algebra/CharP/Two.lean`).
-/

@[expose] public section

section CommSemiring

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]
variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

/-
**frobenius_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：frobenius_def : frobenius R p x = x ^ p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma frobenius_def : frobenius R p x = x ^ p := rfl
/-
**iterateFrobenius_def** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterateFrobenius_def : iterateFrobenius R p n x = x ^ p ^ n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma iterateFrobenius_def : iterateFrobenius R p n x = x ^ p ^ n := rfl
/-
**iterate_frobenius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterate_frobenius : (frobenius R p)^[n] x = x ^ p ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `pow_iterate`：∀ {M : Type u_4} [inst : Monoid M] (k n : ℕ), (fun x => x ^
 k)^[n] = fun x => x ^ k ^ n
-/
lemma iterate_frobenius : (frobenius R p)^[n] x = x ^ p ^ n := congr_fun (pow_iterate p n) x

variable (R)
/-
**iterateFrobenius_eq_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterateFrobenius_eq_pow : iterateFrobenius R p n = frobenius R p ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iterate_frobenius`：iterate_frobenius : (frobenius R p)^[n] x = x ^ p ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iterateFrobenius_eq_pow : iterateFrobenius R p n = frobenius R p ^ n := by
  ext; simp [iterateFrobenius_def, iterate_frobenius]
/-
**coe_iterateFrobenius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_iterateFrobenius : iterateFrobenius R p n = (frobenius R p)^[n]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_iterate`：∀ {M : Type u_4} [inst : Monoid M] (k n : ℕ), (fun x => x ^
 k)^[n] = fun x => x ^ k ^ n
-/
lemma coe_iterateFrobenius : iterateFrobenius R p n = (frobenius R p)^[n] :=
  (pow_iterate p n).symm
/-
**iterateFrobenius_one_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterateFrobenius_one_apply : iterateFrobenius R p 1 x = x ^ p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iterateFrobenius_def`：iterateFrobenius_def : iterateFrobenius R p n x = 
x ^ p ^ n
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma iterateFrobenius_one_apply : iterateFrobenius R p 1 x = x ^ p := by
  rw [iterateFrobenius_def, pow_one]

@[simp]
/-
**iterateFrobenius_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterateFrobenius_one : iterateFrobenius R p 1 = frobenius R p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用引理 `iterateFrobenius_one_apply`：iterateFrobenius_one_apply : iterateFrobeniu
s R p 1 x = x ^ p
-/
lemma iterateFrobenius_one : iterateFrobenius R p 1 = frobenius R p :=
  RingHom.ext (iterateFrobenius_one_apply R p)
/-
**iterateFrobenius_zero_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterateFrobenius_zero_apply : iterateFrobenius R p 0 x = x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iterateFrobenius_def`：iterateFrobenius_def : iterateFrobenius R p n x = 
x ^ p ^ n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma iterateFrobenius_zero_apply : iterateFrobenius R p 0 x = x := by
  rw [iterateFrobenius_def, pow_zero, pow_one]

@[simp]
/-
**iterateFrobenius_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterateFrobenius_zero : iterateFrobenius R p 0 = RingHom.id R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用引理 `iterateFrobenius_zero_apply`：iterateFrobenius_zero_apply : iterateFroben
ius R p 0 x = x
-/
lemma iterateFrobenius_zero : iterateFrobenius R p 0 = RingHom.id R :=
  RingHom.ext (iterateFrobenius_zero_apply R p)
/-
**iterateFrobenius_add_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterateFrobenius_add_apply : iterateFrobenius R p (m + n) x = iterateFrobe
nius R p m (iterateFrobenius R p n x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iterateFrobenius_add_apply :
    iterateFrobenius R p (m + n) x = iterateFrobenius R p m (iterateFrobenius R p n x) := by
  simp_rw [iterateFrobenius_def, add_comm m n, pow_add, pow_mul]
/-
**iterateFrobenius_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterateFrobenius_add : iterateFrobenius R p (m + n) = (iterateFrobenius R 
p m).comp (iterateFrobenius R p n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用引理 `iterateFrobenius_add_apply`：iterateFrobenius_add_apply : iterateFrobeniu
s R p (m + n) x = iterateFrobenius R p m (iterateFrobenius R p n x)
-/
lemma iterateFrobenius_add :
    iterateFrobenius R p (m + n) = (iterateFrobenius R p m).comp (iterateFrobenius R p n) :=
  RingHom.ext (iterateFrobenius_add_apply R p m n)
/-
**iterateFrobenius_mul_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：iterateFrobenius_mul_apply : iterateFrobenius R p (m * n) x = (iterateFrob
enius R p m)^[n] x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `coe_iterateFrobenius`：coe_iterateFrobenius : iterateFrobenius R p n = (f
robenius R p)^[n]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.iterate_mul`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m * n] = 
f^[m] ^[n]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iterateFrobenius_mul_apply :
    iterateFrobenius R p (m * n) x = (iterateFrobenius R p m)^[n] x := by
  simp_rw [coe_iterateFrobenius, Function.iterate_mul]
/-
**coe_iterateFrobenius_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：coe_iterateFrobenius_mul : iterateFrobenius R p (m * n) = (iterateFrobeniu
s R p m)^[n]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `iterateFrobenius_mul_apply`：iterateFrobenius_mul_apply : iterateFrobeniu
s R p (m * n) x = (iterateFrobenius R p m)^[n] x
-/
lemma coe_iterateFrobenius_mul : iterateFrobenius R p (m * n) = (iterateFrobenius R p m)^[n] :=
  funext (iterateFrobenius_mul_apply R p m n)

variable {R}
/-
**MonoidHom.map_frobenius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.map_frobenius : f (frobenius R p x) = frobenius S p (f x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
-/
lemma MonoidHom.map_frobenius : f (frobenius R p x) = frobenius S p (f x) := map_pow f x p
/-
**RingHom.map_frobenius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.map_frobenius : g (frobenius R p x) = frobenius S p (g x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma RingHom.map_frobenius : g (frobenius R p x) = frobenius S p (g x) := map_pow g x p
/-
**MonoidHom.map_iterate_frobenius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.map_iterate_frobenius (n : Nat) : f ((frobenius R p)^[n] x) = (f
robenius S p)^[n] (f x)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Semiconj.iterate_right`：iterate_right {f : α -> β} {ga : α -> α
} {gb : β -> β} (h : Semiconj f ga gb) (n : Nat) : Semiconj f ga^[n] gb^[n]
· 使用引理 `MonoidHom.map_frobenius`：MonoidHom.map_frobenius : f (frobenius R p x) =
 frobenius S p (f x)
-/
lemma MonoidHom.map_iterate_frobenius (n : ℕ) :
    f ((frobenius R p)^[n] x) = (frobenius S p)^[n] (f x) :=
  Function.Semiconj.iterate_right (f.map_frobenius p) n x
/-
**MonoidHom.map_iterateFrobenius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.map_iterateFrobenius (n : Nat) : f (iterateFrobenius R p n x) = 
iterateFrobenius S p n (f x)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma MonoidHom.map_iterateFrobenius (n : ℕ) :
    f (iterateFrobenius R p n x) = iterateFrobenius S p n (f x) := by
  simp [iterateFrobenius_def]
/-
**RingHom.map_iterate_frobenius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.map_iterate_frobenius (n : Nat) : g ((frobenius R p)^[n] x) = (fro
benius S p)^[n] (g x)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.map_iterate_frobenius`：MonoidHom.map_iterate_frobenius (n : Na
t) : f ((frobenius R p)^[n] x) = (frobenius S p)^[n] (f x)
-/
lemma RingHom.map_iterate_frobenius (n : ℕ) :
    g ((frobenius R p)^[n] x) = (frobenius S p)^[n] (g x) :=
  g.toMonoidHom.map_iterate_frobenius p x n
/-
**RingHom.map_iterateFrobenius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.map_iterateFrobenius (n : Nat) : g (iterateFrobenius R p n x) = it
erateFrobenius S p n (g x)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.map_iterateFrobenius`：MonoidHom.map_iterateFrobenius (n : Nat)
 : f (iterateFrobenius R p n x) = iterateFrobenius S p n (f x)
-/
lemma RingHom.map_iterateFrobenius (n : ℕ) :
    g (iterateFrobenius R p n x) = iterateFrobenius S p n (g x) :=
  g.toMonoidHom.map_iterateFrobenius p x n
/-
**MonoidHom.iterate_map_frobenius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonoidHom.iterate_map_frobenius (f : R ->* R) (p : Nat) [ExpChar R p] (n :
 Nat) : f^[n] (frobenius R p x) = frobenius R p (f^[n] x)
参数：f : R ->* R；p : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `iterate_map_pow`：iterate_map_pow {M F : Type*} [Monoid M] [FunLike F M M
] [MonoidHomClass F M M] (f : F) (n : Nat) (x : M) (k : Nat) : f^[n] (x ^ k) = f
^[n] …
-/
lemma MonoidHom.iterate_map_frobenius (f : R →* R) (p : ℕ) [ExpChar R p] (n : ℕ) :
    f^[n] (frobenius R p x) = frobenius R p (f^[n] x) :=
  iterate_map_pow f _ _ _
/-
**RingHom.iterate_map_frobenius** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.iterate_map_frobenius (f : R ->+* R) (p : Nat) [ExpChar R p] (n : 
Nat) : f^[n] (frobenius R p x) = frobenius R p (f^[n] x)
参数：f : R ->+* R；p : Nat；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `iterate_map_pow`：iterate_map_pow {M F : Type*} [Monoid M] [FunLike F M M
] [MonoidHomClass F M M] (f : F) (n : Nat) (x : M) (k : Nat) : f^[n] (x ^ k) = f
^[n] …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma RingHom.iterate_map_frobenius (f : R →+* R) (p : ℕ) [ExpChar R p] (n : ℕ) :
    f^[n] (frobenius R p x) = frobenius R p (f^[n] x) := iterate_map_pow f _ _ _

/-- The Frobenius endomorphism commutes with any ring homomorphism. -/
/-
**RingHom.frobenius_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.frobenius_comm : g.comp (frobenius R p) = (frobenius S p).comp g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用引理 `RingHom.map_frobenius`：RingHom.map_frobenius : g (frobenius R p x) = fro
benius S p (g x)

--- 原说明 ---
The Frobenius endomorphism commutes with any ring homomorphism.
-/
lemma RingHom.frobenius_comm : g.comp (frobenius R p) = (frobenius S p).comp g :=
  ext <| map_frobenius g p

/-- The iterated Frobenius endomorphism commutes with any ring homomorphism. -/
/-
**RingHom.iterateFrobenius_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.iterateFrobenius_comm (n : Nat) : g.comp (iterateFrobenius R p n) 
= (iterateFrobenius S p n).comp g
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用引理 `RingHom.map_iterateFrobenius`：RingHom.map_iterateFrobenius (n : Nat) : g
 (iterateFrobenius R p n x) = iterateFrobenius S p n (g x)

--- 原说明 ---
The iterated Frobenius endomorphism commutes with any ring homomorphism.
-/
lemma RingHom.iterateFrobenius_comm (n : ℕ) :
    g.comp (iterateFrobenius R p n) = (iterateFrobenius S p n).comp g :=
  ext fun x ↦ map_iterateFrobenius g p x n

variable (R S)

/-- The Frobenius map of an algebra as a Frobenius-semilinear map. -/
nonrec def LinearMap.frobenius [Algebra R S] : S →ₛₗ[frobenius R p] S where
  __ := frobenius S p
  map_smul' r s := show frobenius S p _ = _ by
    simp_rw [Algebra.smul_def, map_mul, ← (algebraMap R S).map_frobenius]; rfl

/-- The iterated Frobenius map of an algebra as an iterated-Frobenius-semilinear map. -/
nonrec def LinearMap.iterateFrobenius [Algebra R S] : S →ₛₗ[iterateFrobenius R p n] S where
  __ := iterateFrobenius S p n
  map_smul' f s := show iterateFrobenius S p n _ = _ by
    simp_rw [iterateFrobenius_def, Algebra.smul_def, mul_pow, ← map_pow]; rfl

/-
**LinearMap.frobenius_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.frobenius_def [Algebra R S] (x : S) : frobenius R S p x = x ^ p
参数：x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.frobenius_def [Algebra R S] (x : S) : frobenius R S p x = x ^ p := rfl
/-
**LinearMap.iterateFrobenius_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.iterateFrobenius_def [Algebra R S] (n : Nat) (x : S) : iterateFr
obenius R S p n x = x ^ p ^ n
参数：n : Nat；x : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LinearMap.iterateFrobenius_def [Algebra R S] (n : ℕ) (x : S) :
    iterateFrobenius R S p n x = x ^ p ^ n := rfl

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (p : ℕ) [ExpChar R p] (x y : R)

end CommRing

