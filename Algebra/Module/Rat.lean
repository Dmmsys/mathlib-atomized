/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Field.Rat

/-!
# Basic results about modules over the rationals.
-/

public section

universe u v

variable {M M₂ : Type*}

/-
**map_nnratCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nnratCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLi
ke F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionSemiring R]
 [DivisionSemiring S] [Module R M] [Module S M₂] (c : Rat>=0) (x : M) : f ((c : 
R) • x) = (c : S) • f x
参数：f : F；R S : Type*；c : Rat>=0；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `NNRat.cast_def`：cast_def (q : Rat>=0) : (q : K) = q.num / q.den
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `map_natCast_smul`：map_natCast_smul [AddCommMonoid M] [AddCommMonoid M₂] 
{F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [S
emirin…
· 使用定理 `map_inv_natCast_smul`：map_inv_natCast_smul [AddCommMonoid M] [AddCommMon
oid M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : T
ype*) [Div…
-/
theorem map_nnratCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionSemiring R] [DivisionSemiring S]
    [Module R M] [Module S M₂] (c : ℚ≥0) (x : M) :
    f ((c : R) • x) = (c : S) • f x := by
  rw [NNRat.cast_def, NNRat.cast_def, div_eq_mul_inv, div_eq_mul_inv, mul_smul, mul_smul,
    map_natCast_smul f R S, map_inv_natCast_smul f R S]
/-
**map_ratCast_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_ratCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F
 M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [Divisi
onRing S] [Module R M] [Module S M₂] (c : Rat) (x : M) : f ((c : R) • x) = (c : 
S) • f x
参数：f : F；R S : Type*；c : Rat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.cast_def`：cast_def (q : Rat) : (q : K) = q.num / q.den
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `map_intCast_smul`：map_intCast_smul [AddCommGroup M] [AddCommGroup M₂] {F
 : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Rin
g R] […
· 使用定理 `map_inv_natCast_smul`：map_inv_natCast_smul [AddCommMonoid M] [AddCommMon
oid M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : T
ype*) [Div…
-/
theorem map_ratCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (c : ℚ) (x : M) :
    f ((c : R) • x) = (c : S) • f x := by
  rw [Rat.cast_def, Rat.cast_def, div_eq_mul_inv, div_eq_mul_inv, mul_smul, mul_smul,
    map_intCast_smul f R S, map_inv_natCast_smul f R S]
/-
**map_nnrat_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_nnrat_smul [AddCommMonoid M] [AddCommMonoid M₂] [_instM : Module Rat>=
0 M] [_instM₂ : Module Rat>=0 M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClas
s F M M₂] (f : F) (c : Rat>=0) (x : M) : f (c • x) = c • f x
参数：f : F；c : Rat>=0；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nnratCast_smul`：map_nnratCast_smul [AddCommMonoid M] [AddCommMonoid 
M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*
) [Divis…
-/
theorem map_nnrat_smul [AddCommMonoid M] [AddCommMonoid M₂]
    [_instM : Module ℚ≥0 M] [_instM₂ : Module ℚ≥0 M₂]
    {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂]
    (f : F) (c : ℚ≥0) (x : M) : f (c • x) = c • f x :=
  map_nnratCast_smul f ℚ≥0 ℚ≥0 c x
/-
**map_rat_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_rat_smul [AddCommGroup M] [AddCommGroup M₂] [_instM : Module Rat M] [_
instM₂ : Module Rat M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] 
(f : F) (c : Rat) (x : M) : f (c • x) = c • f x
参数：f : F；c : Rat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ratCast_smul`：map_ratCast_smul [AddCommGroup M] [AddCommGroup M₂] {F
 : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Div
isionR…
-/
theorem map_rat_smul [AddCommGroup M] [AddCommGroup M₂]
    [_instM : Module ℚ M] [_instM₂ : Module ℚ M₂]
    {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂]
    (f : F) (c : ℚ) (x : M) : f (c • x) = c • f x :=
  map_ratCast_smul f ℚ ℚ c x

/-- There can be at most one `Module ℚ≥0 E` structure on an additive commutative monoid. -/
/-
**subsingleton_nnrat_module** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：subsingleton_nnrat_module (E : Type*) [AddCommMonoid E] : Subsingleton (Mo
dule Rat>=0 E)
参数：E : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.ext'`：Module.ext' {R : Type*} [Semiring R] {M : Type*} [AddCommMo
noid M] (P Q : Module R M) (w : forall (r : R) (m : M), (haveI
· 使用定理 `map_nnrat_smul`：map_nnrat_smul [AddCommMonoid M] [AddCommMonoid M₂] [_in
stM : Module Rat>=0 M] [_instM₂ : Module Rat>=0 M₂] {F : Type*} [FunLike F M M₂]
 [Ad…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
There can be at most one `Module ℚ≥0 E` structure on an additive commutative mon
oid.
-/
instance subsingleton_nnrat_module (E : Type*) [AddCommMonoid E] : Subsingleton (Module ℚ≥0 E) :=
  ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_nnrat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩

/-- There can be at most one `Module ℚ E` structure on an additive commutative group. -/
/-
**subsingleton_rat_module** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：subsingleton_rat_module (E : Type*) [AddCommGroup E] : Subsingleton (Modul
e Rat E)
参数：E : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.ext'`：Module.ext' {R : Type*} [Semiring R] {M : Type*} [AddCommMo
noid M] (P Q : Module R M) (w : forall (r : R) (m : M), (haveI
· 使用定理 `map_rat_smul`：map_rat_smul [AddCommGroup M] [AddCommGroup M₂] [_instM : 
Module Rat M] [_instM₂ : Module Rat M₂] {F : Type*} [FunLike F M M₂] [AddMonoidH
om…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
There can be at most one `Module ℚ E` structure on an additive commutative group
.
-/
instance subsingleton_rat_module (E : Type*) [AddCommGroup E] : Subsingleton (Module ℚ E) :=
  ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_rat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩

/-- If `E` is a vector space over two division semirings `R` and `S`, then scalar multiplications
agree on non-negative rational numbers in `R` and `S`. -/
/-
**nnratCast_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nnratCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSem
iring R] [DivisionSemiring S] [Module R E] [Module S E] (r : Rat>=0) (x : E) : (
r : R) • x = (r : S) • x
参数：R S : Type*；r : Rat>=0；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nnratCast_smul`：map_nnratCast_smul [AddCommMonoid M] [AddCommMonoid 
M₂] {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*
) [Divis…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `E` is a vector space over two division semirings `R` and `S`, then scalar mu
ltiplications
agree on non-negative rational numbers in `R` and `S`.
-/
theorem nnratCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [DivisionSemiring S] [Module R E] [Module S E] (r : ℚ≥0) (x : E) : (r : R) • x = (r : S) • x :=
  map_nnratCast_smul (AddMonoidHom.id E) R S r x

/-- If `E` is a vector space over two division rings `R` and `S`, then scalar multiplications
agree on rational numbers in `R` and `S`. -/
/-
**ratCast_smul_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ratCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R
] [DivisionRing S] [Module R E] [Module S E] (r : Rat) (x : E) : (r : R) • x = (
r : S) • x
参数：R S : Type*；r : Rat；x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_ratCast_smul`：map_ratCast_smul [AddCommGroup M] [AddCommGroup M₂] {F
 : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [Div
isionR…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `E` is a vector space over two division rings `R` and `S`, then scalar multip
lications
agree on rational numbers in `R` and `S`.
-/
theorem ratCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (r : ℚ) (x : E) : (r : R) • x = (r : S) • x :=
  map_ratCast_smul (AddMonoidHom.id E) R S r x
/-
**IsScalarTower.nnrat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsScalarTower.nnrat {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid 
M] [Module R M] [Module Rat>=0 R] [Module Rat>=0 M] : IsScalarTower Rat>=0 R M w
here smul_assoc r x y
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `map_nnrat_smul`：map_nnrat_smul [AddCommMonoid M] [AddCommMonoid M₂] [_in
stM : Module Rat>=0 M] [_instM₂ : Module Rat>=0 M₂] {F : Type*} [FunLike F M M₂]
 [Ad…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
instance IsScalarTower.nnrat {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    [Module ℚ≥0 R] [Module ℚ≥0 M] : IsScalarTower ℚ≥0 R M where
  smul_assoc r x y := map_nnrat_smul ((smulAddHom R M).flip y) r x
/-
**IsScalarTower.rat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsScalarTower.rat {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Mod
ule R M] [Module Rat R] [Module Rat M] : IsScalarTower Rat R M where smul_assoc 
r x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `map_rat_smul`：map_rat_smul [AddCommGroup M] [AddCommGroup M₂] [_instM : 
Module Rat M] [_instM₂ : Module Rat M₂] {F : Type*} [FunLike F M M₂] [AddMonoidH
om…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
instance IsScalarTower.rat {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    [Module ℚ R] [Module ℚ M] : IsScalarTower ℚ R M where
  smul_assoc r x y := map_rat_smul ((smulAddHom R M).flip y) r x

/-- `nnqsmul` is equal to any other module structure via a cast. -/
/-
**NNRat.cast_smul_eq_nnqsmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NNRat.cast_smul_eq_nnqsmul (R : Type*) [DivisionSemiring R] [MulAction R M
] [MulAction Rat>=0 M] [IsScalarTower Rat>=0 R M] (q : Rat>=0) (x : M) : (q : R)
 • x = q • x
参数：R : Type*；q : Rat>=0；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `NNRat.smul_one_eq_cast`：∀ (K : Type u_1) [inst : DivisionSemiring K] (q 
: ℚ≥0), q • 1 = ↑q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`nnqsmul` is equal to any other module structure via a cast.
-/
lemma NNRat.cast_smul_eq_nnqsmul (R : Type*) [DivisionSemiring R]
    [MulAction R M] [MulAction ℚ≥0 M] [IsScalarTower ℚ≥0 R M]
    (q : ℚ≥0) (x : M) : (q : R) • x = q • x := by
  rw [← one_smul R x, ← smul_assoc, ← smul_assoc]; simp

/-- `qsmul` is equal to any other module structure via a cast. -/
/-
**Rat.cast_smul_eq_qsmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Rat.cast_smul_eq_qsmul (R : Type*) [DivisionRing R] [MulAction R M] [MulAc
tion Rat M] [IsScalarTower Rat R M] (q : Rat) (x : M) : (q : R) • x = q • x
参数：R : Type*；q : Rat；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Rat.smul_one_eq_cast`：smul_one_eq_cast (A : Type*) [DivisionRing A] (m :
 Rat) : m • (1 : A) = ↑m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`qsmul` is equal to any other module structure via a cast.
-/
lemma Rat.cast_smul_eq_qsmul (R : Type*) [DivisionRing R]
    [MulAction R M] [MulAction ℚ M] [IsScalarTower ℚ R M]
    (q : ℚ) (x : M) : (q : R) • x = q • x := by
  rw [← one_smul R x, ← smul_assoc, ← smul_assoc]; simp

section
variable {α : Type u} {M : Type v}

/-
**SMulCommClass.nnrat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SMulCommClass.nnrat [AddCommMonoid M] [DistribSMul α M] [Module Rat>=0 M] 
: SMulCommClass Rat>=0 α M where smul_comm r x y
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_nnrat_smul`：map_nnrat_smul [AddCommMonoid M] [AddCommMonoid M₂] [_in
stM : Module Rat>=0 M] [_instM₂ : Module Rat>=0 M₂] {F : Type*} [FunLike F M M₂]
 [Ad…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
instance SMulCommClass.nnrat [AddCommMonoid M] [DistribSMul α M] [Module ℚ≥0 M] :
    SMulCommClass ℚ≥0 α M where
  smul_comm r x y := (map_nnrat_smul (DistribSMul.toAddMonoidHom M x) r y).symm
/-
**SMulCommClass.rat** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SMulCommClass.rat [AddCommGroup M] [DistribSMul α M] [Module Rat M] : SMul
CommClass Rat α M where smul_comm r x y
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_rat_smul`：map_rat_smul [AddCommGroup M] [AddCommGroup M₂] [_instM : 
Module Rat M] [_instM₂ : Module Rat M₂] {F : Type*} [FunLike F M M₂] [AddMonoidH
om…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
instance SMulCommClass.rat [AddCommGroup M] [DistribSMul α M] [Module ℚ M] :
    SMulCommClass ℚ α M where
  smul_comm r x y := (map_rat_smul (DistribSMul.toAddMonoidHom M x) r y).symm
/-
**SMulCommClass.nnrat'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SMulCommClass.nnrat' [AddCommMonoid M] [DistribSMul α M] [Module Rat>=0 M]
 : SMulCommClass α Rat>=0 M
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance SMulCommClass.nnrat' [AddCommMonoid M] [DistribSMul α M] [Module ℚ≥0 M] :
    SMulCommClass α ℚ≥0 M :=
  SMulCommClass.symm _ _ _
/-
**SMulCommClass.rat'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：SMulCommClass.rat' [AddCommGroup M] [DistribSMul α M] [Module Rat M] : SMu
lCommClass α Rat M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance SMulCommClass.rat' [AddCommGroup M] [DistribSMul α M] [Module ℚ M] :
    SMulCommClass α ℚ M :=
  SMulCommClass.symm _ _ _

end

variable (M) in
/-- A `ℚ≥0`-module is torsion-free as a group.

This instance will fire for any monoid `M`, so is local unless needed elsewhere. -/
/-
**IsAddTorsionFree.of_module_nnrat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAddTorsionFree.of_module_nnrat [AddCommMonoid M] [Module Rat>=0 M] : IsA
ddTorsionFree M where nsmul_right_injective n hn x y hxy
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
A `ℚ≥0`-module is torsion-free as a group.

This instance will fire for any monoid `M`, so is local unless needed elsewhere.
-/
lemma IsAddTorsionFree.of_module_nnrat [AddCommMonoid M] [Module ℚ≥0 M] : IsAddTorsionFree M where
  nsmul_right_injective n hn x y hxy := by
    simpa [← Nat.cast_smul_eq_nsmul ℚ≥0 n, *] using congr((n⁻¹ : ℚ≥0) • $hxy)

variable (M) in
/-- A `ℚ≥0`-module is torsion-free as a group.

This instance will fire for any monoid `M`, so is local unless needed elsewhere. -/
/-
**IsAddTorsionFree.of_module_rat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAddTorsionFree.of_module_rat [AddCommGroup M] [Module Rat M] : IsAddTors
ionFree M where nsmul_right_injective n hn x y hxy
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
A `ℚ≥0`-module is torsion-free as a group.

This instance will fire for any monoid `M`, so is local unless needed elsewhere.
-/
lemma IsAddTorsionFree.of_module_rat [AddCommGroup M] [Module ℚ M] : IsAddTorsionFree M where
  nsmul_right_injective n hn x y hxy := by
    simpa [← Nat.cast_smul_eq_nsmul ℚ n, *] using congr((n⁻¹ : ℚ) • $hxy)
