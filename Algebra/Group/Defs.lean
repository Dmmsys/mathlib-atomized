/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro
-/
module

public import Batteries.Logic
public import Batteries.Util.LibraryNote
public import Mathlib.Algebra.Notation.Defs
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.BinaryRec
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Tactic.OfNat
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Simps.Basic
public import Mathlib.Tactic.AdaptationNote
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Typeclasses for (semi)groups and monoids

In this file we define typeclasses for algebraic structures with one binary operation.
The classes are named `(Add)?(Comm)?(Semigroup|Monoid|Group)`, where `Add` means that
the class uses additive notation and `Comm` means that the class assumes that the binary
operation is commutative.

The file does not contain any lemmas except for

* axioms of typeclasses restated in the root namespace;
* lemmas required for instances.

For basic lemmas about these classes see `Mathlib/Algebra/Group/Basic.lean`.

We register the following instances:

- `Pow M ℕ`, for monoids `M`, and `Pow G ℤ` for groups `G`;
- `SMul ℕ M` for additive monoids `M`, and `SMul ℤ G` for additive groups `G`.

## Notation

- `+`, `-`, `*`, `/`, `^` : the usual arithmetic operations; the underlying functions are
  `Add.add`, `Neg.neg`/`Sub.sub`, `Mul.mul`, `Div.div`, and `HPow.hPow`.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered Function.const_injective

universe u v w

open Function

variable {G : Type*}

section Mul

variable [Mul G]

/--
Definition of `IsLeftCancelMul` / `IsLeftCancelMul` 的定义

English:
class IsLeftCancelMul
  parameters: (G : Type u) [Mul G]
  axioms and operations (1):
    - mul_left_cancel((a : G)) : IsLeftRegular a

中文:
类 IsLeftCancelMul
  参数: (G : 类型u) [Mul G]
  公理与运算 (1 个):
    - mul_left_cancel((a : G)) : IsLeftRegular a
-/
@[mk_iff] class IsLeftCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is left cancellative (i.e. left regular). -/
  protected mul_left_cancel (a : G) : IsLeftRegular a
/--
Definition of `IsRightCancelMul` / `IsRightCancelMul` 的定义

English:
class IsRightCancelMul
  parameters: (G : Type u) [Mul G]
  axioms and operations (1):
    - mul_right_cancel((a : G)) : IsRightRegular a

中文:
类 IsRightCancelMul
  参数: (G : 类型u) [Mul G]
  公理与运算 (1 个):
    - mul_right_cancel((a : G)) : IsRightRegular a
-/
@[mk_iff] class IsRightCancelMul (G : Type u) [Mul G] : Prop where
  /-- Multiplication is right cancellative (i.e. right regular). -/
  protected mul_right_cancel (a : G) : IsRightRegular a
/-- A mixin for cancellative multiplication. -/
@[mk_iff]
/--
Definition of `IsCancelMul` / `IsCancelMul` 的定义

English:
class IsCancelMul
  parameters: (G : Type u) [Mul G]
  extends: IsLeftCancelMul G, IsRightCancelMul G
  (no additional axioms)

中文:
类 IsCancelMul
  参数: (G : 类型u) [Mul G]
  继承: IsLeftCancelMul G, IsRightCancelMul G
  (无附加公理)
-/
class IsCancelMul (G : Type u) [Mul G] : Prop extends IsLeftCancelMul G, IsRightCancelMul G

/--
Definition of `IsLeftCancelAdd` / `IsLeftCancelAdd` 的定义

English:
class IsLeftCancelAdd
  parameters: (G : Type u) [Add G]
  axioms and operations (1):
    - add_left_cancel((a : G)) : IsAddLeftRegular a

中文:
类 IsLeftCancelAdd
  参数: (G : 类型u) [Add G]
  公理与运算 (1 个):
    - add_left_cancel((a : G)) : IsAddLeftRegular a
-/
class IsLeftCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is left cancellative (i.e. left regular). -/
  protected add_left_cancel (a : G) : IsAddLeftRegular a

attribute [to_additive] IsLeftCancelMul
attribute [to_additive] isLeftCancelMul_iff

/--
Definition of `IsRightCancelAdd` / `IsRightCancelAdd` 的定义

English:
class IsRightCancelAdd
  parameters: (G : Type u) [Add G]
  axioms and operations (1):
    - add_right_cancel((a : G)) : IsAddRightRegular a

中文:
类 IsRightCancelAdd
  参数: (G : 类型u) [Add G]
  公理与运算 (1 个):
    - add_right_cancel((a : G)) : IsAddRightRegular a
-/
class IsRightCancelAdd (G : Type u) [Add G] : Prop where
  /-- Addition is right cancellative (i.e. right regular). -/
  protected add_right_cancel (a : G) : IsAddRightRegular a

attribute [to_additive] IsRightCancelMul
attribute [to_additive] isRightCancelMul_iff

/-- A mixin for cancellative addition. -/
@[mk_iff]
/--
Definition of `IsCancelAdd` / `IsCancelAdd` 的定义

English:
class IsCancelAdd
  parameters: (G : Type u) [Add G]
  extends: IsLeftCancelAdd G, IsRightCancelAdd G
  (no additional axioms)

中文:
类 IsCancelAdd
  参数: (G : 类型u) [Add G]
  继承: IsLeftCancelAdd G, IsRightCancelAdd G
  (无附加公理)
-/
class IsCancelAdd (G : Type u) [Add G] : Prop extends IsLeftCancelAdd G, IsRightCancelAdd G

attribute [to_additive] IsCancelMul
attribute [to_additive existing] isCancelMul_iff

section Regular

variable {R : Type*}

/--
theorem `isCancelMul_iff_forall_isRegular` / 定理 `isCancelMul_iff_forall_isRegular`

English:
theorem isCancelMul_iff_forall_isRegular
  given: [Mul R]
  proof: by
  rw [isCancelMul_iff]; rw [isLeftCancelMul_iff]; rw [isRightCancelMul_iff]; rw [← forall_and]
  exact forall_congr' fun _ => isRegular_iff.symm

中文:
定理 isCancelMul_iff_forall_isRegular
  条件: [Mul R]
  证明: by
  rw [isCancelMul_iff]; rw [isLeftCancelMul_iff]; rw [isRightCancelMul_iff]; rw [← forall_and]
  exact forall_congr' fun _ => isRegular_iff.symm
-/
@[to_additive] theorem isCancelMul_iff_forall_isRegular [Mul R] :
    IsCancelMul R ↔ forall r : R, IsRegular r := by
  rw [isCancelMul_iff]; rw [isLeftCancelMul_iff]; rw [isRightCancelMul_iff]; rw [← forall_and]
  exact forall_congr' fun _ => isRegular_iff.symm

/-- If all multiplications cancel on the left then every element is left-regular. -/
@[to_additive /-- If all additions cancel on the left then every element is add-left-regular. -/]
/--
theorem `IsLeftRegular.all` / 定理 `IsLeftRegular.all`

English:
theorem IsLeftRegular.all
  given: [Mul R] [IsLeftCancelMul R] (g : R)
  statement: IsLeftRegular g
  proof: (isLeftCancelMul_iff R).mp ‹_› _

中文:
定理 IsLeftRegular.all
  条件: [Mul R] [IsLeftCancelMul R] (g : R)
  结论: IsLeftRegular g
  证明: (isLeftCancelMul_iff R).mp ‹_› _

Depends on / 依赖: isLeftCancelMul_iff
-/
theorem IsLeftRegular.all [Mul R] [IsLeftCancelMul R] (g : R) : IsLeftRegular g :=
  (isLeftCancelMul_iff R).mp ‹_› _

/-- If all multiplications cancel on the right then every element is right-regular. -/
@[to_additive /-- If all additions cancel on the right then every element is add-right-regular. -/]
/--
theorem `IsRightRegular.all` / 定理 `IsRightRegular.all`

English:
theorem IsRightRegular.all
  given: [Mul R] [IsRightCancelMul R] (g : R)
  statement: IsRightRegular g
  proof: (isRightCancelMul_iff R).mp ‹_› _

中文:
定理 IsRightRegular.all
  条件: [Mul R] [IsRightCancelMul R] (g : R)
  结论: IsRightRegular g
  证明: (isRightCancelMul_iff R).mp ‹_› _

Depends on / 依赖: isRightCancelMul_iff
-/
theorem IsRightRegular.all [Mul R] [IsRightCancelMul R] (g : R) : IsRightRegular g :=
  (isRightCancelMul_iff R).mp ‹_› _

/-- If all multiplications cancel then every element is regular. -/
@[to_additive /-- If all additions cancel then every element is add-regular. -/]
/--
theorem `IsRegular.all` / 定理 `IsRegular.all`

English:
theorem IsRegular.all
  given: [Mul R] [IsCancelMul R] (g : R)
  statement: IsRegular g
  proof: ⟨.all g, .all g⟩

中文:
定理 IsRegular.all
  条件: [Mul R] [IsCancelMul R] (g : R)
  结论: IsRegular g
  证明: ⟨.all g, .all g⟩
-/
theorem IsRegular.all [Mul R] [IsCancelMul R] (g : R) : IsRegular g := ⟨.all g, .all g⟩

end Regular

section IsLeftCancelMul

variable [IsLeftCancelMul G] {a b c : G}

@[to_additive]
/--
theorem `mul_left_cancel` / 定理 `mul_left_cancel`

English:
theorem mul_left_cancel
  statement: a * b = a * c -> b = c
  proof: (IsLeftCancelMul.mul_left_cancel a ·)

@[to_additive]

中文:
定理 mul_left_cancel
  结论: a * b = a * c -> b = c
  证明: (IsLeftCancelMul.mul_left_cancel a ·)

@[to_additive]

Depends on / 依赖: IsLeftCancelMul, IsLeftCancelMul.mul_left_cancel, mul_left_cancel
-/
theorem mul_left_cancel : a * b = a * c -> b = c :=
  (IsLeftCancelMul.mul_left_cancel a ·)

@[to_additive]
/--
theorem `mul_left_cancel_iff` / 定理 `mul_left_cancel_iff`

English:
theorem mul_left_cancel_iff
  statement: a * b = a * c ↔ b = c
  proof: ⟨mul_left_cancel, congrArg _⟩

@[to_additive]

中文:
定理 mul_left_cancel_iff
  结论: a * b = a * c ↔ b = c
  证明: ⟨mul_left_cancel, congrArg _⟩

@[to_additive]

Depends on / 依赖: mul_left_cancel
-/
theorem mul_left_cancel_iff : a * b = a * c ↔ b = c :=
  ⟨mul_left_cancel, congrArg _⟩

@[to_additive]
/--
theorem `mul_right_injective` / 定理 `mul_right_injective`

English:
theorem mul_right_injective
  given: (a : G)
  statement: Injective (a * ·)
  proof: fun _ _ => mul_left_cancel

@[to_additive (attr := simp)]

中文:
定理 mul_right_injective
  条件: (a : G)
  结论: Injective (a * ·)
  证明: fun _ _ => mul_left_cancel

@[to_additive (attr := simp)]

Depends on / 依赖: mul_left_cancel
-/
theorem mul_right_injective (a : G) : Injective (a * ·) := fun _ _ => mul_left_cancel

@[to_additive (attr := simp)]
/--
theorem `mul_right_inj` / 定理 `mul_right_inj`

English:
theorem mul_right_inj
  given: (a : G) {b c : G}
  statement: a * b = a * c ↔ b = c
  proof: (mul_right_injective a).eq_iff

@[to_additive]

中文:
定理 mul_right_inj
  条件: (a : G) {b c : G}
  结论: a * b = a * c ↔ b = c
  证明: (mul_right_injective a).eq_iff

@[to_additive]

Depends on / 依赖: eq_iff, mul_right_injective
-/
theorem mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c :=
  (mul_right_injective a).eq_iff

@[to_additive]
/--
theorem `mul_ne_mul_right` / 定理 `mul_ne_mul_right`

English:
theorem mul_ne_mul_right
  given: (a : G) {b c : G}
  statement: a * b != a * c ↔ b != c
  proof: (mul_right_injective a).ne_iff

中文:
定理 mul_ne_mul_right
  条件: (a : G) {b c : G}
  结论: a * b != a * c ↔ b != c
  证明: (mul_right_injective a).ne_iff

Depends on / 依赖: mul_right_injective, ne_iff
-/
theorem mul_ne_mul_right (a : G) {b c : G} : a * b != a * c ↔ b != c :=
  (mul_right_injective a).ne_iff

end IsLeftCancelMul

section IsRightCancelMul

variable [IsRightCancelMul G] {a b c : G}

@[to_additive]
/--
theorem `mul_right_cancel` / 定理 `mul_right_cancel`

English:
theorem mul_right_cancel
  statement: a * b = c * b -> a = c
  proof: (IsRightCancelMul.mul_right_cancel b ·)

@[to_additive]

中文:
定理 mul_right_cancel
  结论: a * b = c * b -> a = c
  证明: (IsRightCancelMul.mul_right_cancel b ·)

@[to_additive]

Depends on / 依赖: IsRightCancelMul, IsRightCancelMul.mul_right_cancel, mul_right_cancel
-/
theorem mul_right_cancel : a * b = c * b -> a = c :=
  (IsRightCancelMul.mul_right_cancel b ·)

@[to_additive]
/--
theorem `mul_right_cancel_iff` / 定理 `mul_right_cancel_iff`

English:
theorem mul_right_cancel_iff
  statement: b * a = c * a ↔ b = c
  proof: ⟨mul_right_cancel, congrArg (· * a)⟩

@[to_additive]

中文:
定理 mul_right_cancel_iff
  结论: b * a = c * a ↔ b = c
  证明: ⟨mul_right_cancel, congrArg (· * a)⟩

@[to_additive]

Depends on / 依赖: mul_right_cancel
-/
theorem mul_right_cancel_iff : b * a = c * a ↔ b = c :=
  ⟨mul_right_cancel, congrArg (· * a)⟩

@[to_additive]
/--
theorem `mul_left_injective` / 定理 `mul_left_injective`

English:
theorem mul_left_injective
  given: (a : G)
  statement: Function.Injective (· * a)
  proof: fun _ _ => mul_right_cancel

@[to_additive (attr := simp)]

中文:
定理 mul_left_injective
  条件: (a : G)
  结论: Function.Injective (· * a)
  证明: fun _ _ => mul_right_cancel

@[to_additive (attr := simp)]

Depends on / 依赖: mul_right_cancel
-/
theorem mul_left_injective (a : G) : Function.Injective (· * a) := fun _ _ => mul_right_cancel

@[to_additive (attr := simp)]
/--
theorem `mul_left_inj` / 定理 `mul_left_inj`

English:
theorem mul_left_inj
  given: (a : G) {b c : G}
  statement: b * a = c * a ↔ b = c
  proof: (mul_left_injective a).eq_iff

@[to_additive]

中文:
定理 mul_left_inj
  条件: (a : G) {b c : G}
  结论: b * a = c * a ↔ b = c
  证明: (mul_left_injective a).eq_iff

@[to_additive]

Depends on / 依赖: eq_iff, mul_left_injective
-/
theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
  (mul_left_injective a).eq_iff

@[to_additive]
/--
theorem `mul_ne_mul_left` / 定理 `mul_ne_mul_left`

English:
theorem mul_ne_mul_left
  given: (a : G) {b c : G}
  statement: b * a != c * a ↔ b != c
  proof: (mul_left_injective a).ne_iff

中文:
定理 mul_ne_mul_left
  条件: (a : G) {b c : G}
  结论: b * a != c * a ↔ b != c
  证明: (mul_left_injective a).ne_iff

Depends on / 依赖: mul_left_injective, ne_iff
-/
theorem mul_ne_mul_left (a : G) {b c : G} : b * a != c * a ↔ b != c :=
  (mul_left_injective a).ne_iff

end IsRightCancelMul

end Mul

/-- A semigroup is a type with an associative `(*)`. -/
@[ext]
/--
Definition of `Semigroup` / `Semigroup` 的定义

English:
class Semigroup
  parameters: (G : Type u)
  extends: Mul G
  axioms and operations (1):
    - mul_assoc : forall a b c : G, a * b * c = a * (b * c)

中文:
类 Semigroup
  参数: (G : 类型u)
  继承: Mul G
  公理与运算 (1 个):
    - mul_assoc : 对任意 a b c : G, a * b * c = a * (b * c)
-/
class Semigroup (G : Type u) extends Mul G where
  /-- Multiplication is associative -/
  protected mul_assoc : forall a b c : G, a * b * c = a * (b * c)

/-- An additive semigroup is a type with an associative `(+)`. -/
@[ext]
/--
Definition of `AddSemigroup` / `AddSemigroup` 的定义

English:
class AddSemigroup
  parameters: (G : Type u)
  extends: Add G
  axioms and operations (1):
    - add_assoc : forall a b c : G, a + b + c = a + (b + c)

中文:
类 AddSemigroup
  参数: (G : 类型u)
  继承: Add G
  公理与运算 (1 个):
    - add_assoc : 对任意 a b c : G, a + b + c = a + (b + c)
-/
class AddSemigroup (G : Type u) extends Add G where
  /-- Addition is associative -/
  protected add_assoc : forall a b c : G, a + b + c = a + (b + c)

attribute [to_additive] Semigroup

section Semigroup

variable [Semigroup G]

@[to_additive]
/--
theorem `mul_assoc` / 定理 `mul_assoc`

English:
theorem mul_assoc
  statement: forall a b c : G, a * b * c = a * (b * c)
  proof: Semigroup.mul_assoc

中文:
定理 mul_assoc
  结论: 对任意 a b c : G, a * b * c = a * (b * c)
  证明: Semigroup.mul_assoc

Depends on / 依赖: Mul.toSMulMulOpposite, Semigroup, Semigroup.mul_assoc, mul_assoc, toSMulMulOpposite
-/
theorem mul_assoc : forall a b c : G, a * b * c = a * (b * c) :=
  Semigroup.mul_assoc

end Semigroup

section IsCommutative

/--
Definition of `IsAddCommutative` / `IsAddCommutative` 的定义

English:
class IsAddCommutative
  parameters: (M : Type*) [Add M]
  axioms and operations (1):
    - is_comm : Std.Commutative (α := M) (· + ·)

中文:
类 IsAddCommutative
  参数: (M : 类型) [Add M]
  公理与运算 (1 个):
    - is_comm : Std.Commutative (α := M) (· + ·)
-/
class IsAddCommutative (M : Type*) [Add M] : Prop where
  is_comm : Std.Commutative (α := M) (· + ·)

/-- A Prop stating that the multiplication is commutative. -/
@[to_additive existing]
/--
Definition of `IsMulCommutative` / `IsMulCommutative` 的定义

English:
class IsMulCommutative
  parameters: (M : Type*) [Mul M]
  axioms and operations (1):
    - is_comm : Std.Commutative (α := M) (· * ·)

中文:
类 IsMulCommutative
  参数: (M : 类型) [Mul M]
  公理与运算 (1 个):
    - is_comm : Std.Commutative (α := M) (· * ·)
-/
class IsMulCommutative (M : Type*) [Mul M] : Prop where
  is_comm : Std.Commutative (α := M) (· * ·)

attribute [instance] IsAddCommutative.is_comm
attribute [instance] IsMulCommutative.is_comm

@[to_additive]
/--
lemma `isMulCommutative_iff` / 引理 `isMulCommutative_iff`

English:
lemma isMulCommutative_iff
  given: {M : Type*} [Mul M]
  statement: IsMulCommutative M ↔ forall a b : M, a * b = b * a
  proof: by
  grind [IsMulCommutative, Std.Commutative]

@[to_additive]
alias ⟨_, IsMulCommutative.of_comm⟩ := isMulCommutative_iff

中文:
引理 isMulCommutative_iff
  条件: {M : 类型} [Mul M]
  结论: IsMulCommutative M ↔ 对任意 a b : M, a * b = b * a
  证明: by
  grind [IsMulCommutative, Std.Commutative]

@[to_additive]
alias ⟨_, IsMulCommutative.of_comm⟩ := isMulCommutative_iff

Depends on / 依赖: Commutative, IsMulCommutative, Std.Commutative
-/
lemma isMulCommutative_iff {M : Type*} [Mul M] : IsMulCommutative M ↔ forall a b : M, a * b = b * a := by
  grind [IsMulCommutative, Std.Commutative]

@[to_additive]
alias ⟨_, IsMulCommutative.of_comm⟩ := isMulCommutative_iff

/-- An alternative to `mul_comm` which uses the mixin `IsMulCommutative` instead of bundled
commutative algebraic structures. In general, you should prefer `mul_comm` unless you are working
with commutative subobjects in a noncommutative algebraic structure. -/
@[to_additive
/-- An alternative to `add_comm` which uses the mixin `IsAddCommutative` instead of bundled
commutative algebraic structures. In general, you should prefer `add_comm` unless you are working
with commutative subobjects in a noncommutative algebraic structure. -/ ]
/--
lemma `mul_comm'` / 引理 `mul_comm'`

English:
lemma mul_comm'
  given: {M : Type*} [Mul M] [IsMulCommutative M] (a b : M)
  statement: a * b = b * a
  proof: IsMulCommutative.is_comm.comm ..

中文:
引理 mul_comm'
  条件: {M : 类型} [Mul M] [IsMulCommutative M] (a b : M)
  结论: a * b = b * a
  证明: IsMulCommutative.is_comm.comm ..

Depends on / 依赖: IsMulCommutative, IsMulCommutative.is_comm.comm, is_comm
-/
lemma mul_comm' {M : Type*} [Mul M] [IsMulCommutative M] (a b : M) : a * b = b * a :=
  IsMulCommutative.is_comm.comm ..

end IsCommutative

/-- A commutative additive magma is a type with an addition which commutes. -/
@[ext]
/--
Definition of `AddCommMagma` / `AddCommMagma` 的定义

English:
class AddCommMagma
  parameters: (G : Type u)
  extends: Add G
  axioms and operations (1):
    - add_comm : forall a b : G, a + b = b + a

中文:
类 AddCommMagma
  参数: (G : 类型u)
  继承: Add G
  公理与运算 (1 个):
    - add_comm : 对任意 a b : G, a + b = b + a
-/
class AddCommMagma (G : Type u) extends Add G where
  /-- Addition is commutative in a commutative additive magma. -/
  protected add_comm : forall a b : G, a + b = b + a

/-- A commutative multiplicative magma is a type with a multiplication which commutes. -/
@[ext]
/--
Definition of `CommMagma` / `CommMagma` 的定义

English:
class CommMagma
  parameters: (G : Type u)
  extends: Mul G
  axioms and operations (1):
    - mul_comm : forall a b : G, a * b = b * a

中文:
类 CommMagma
  参数: (G : 类型u)
  继承: Mul G
  公理与运算 (1 个):
    - mul_comm : 对任意 a b : G, a * b = b * a
-/
class CommMagma (G : Type u) extends Mul G where
  /-- Multiplication is commutative in a commutative multiplicative magma. -/
  protected mul_comm : forall a b : G, a * b = b * a

attribute [to_additive] CommMagma

/-- A commutative semigroup is a type with an associative commutative `(*)`. -/
@[ext]
/--
Definition of `CommSemigroup` / `CommSemigroup` 的定义

English:
class CommSemigroup
  parameters: (G : Type u)
  extends: Semigroup G, CommMagma G
  (no additional axioms)

中文:
类 CommSemigroup
  参数: (G : 类型u)
  继承: Semigroup G, CommMagma G
  (无附加公理)
-/
class CommSemigroup (G : Type u) extends Semigroup G, CommMagma G where

/-- A commutative additive semigroup is a type with an associative commutative `(+)`. -/
@[ext]
/--
Definition of `AddCommSemigroup` / `AddCommSemigroup` 的定义

English:
class AddCommSemigroup
  parameters: (G : Type u)
  extends: AddSemigroup G, AddCommMagma G
  (no additional axioms)

中文:
类 AddCommSemigroup
  参数: (G : 类型u)
  继承: AddSemigroup G, AddCommMagma G
  (无附加公理)
-/
class AddCommSemigroup (G : Type u) extends AddSemigroup G, AddCommMagma G where

attribute [to_additive] CommSemigroup

section CommMagma

variable [CommMagma G] {a : G}

@[to_additive]
/--
theorem `mul_comm` / 定理 `mul_comm`

English:
theorem mul_comm
  statement: forall a b : G, a * b = b * a
  proof: CommMagma.mul_comm

@[to_additive]

中文:
定理 mul_comm
  结论: 对任意 a b : G, a * b = b * a
  证明: CommMagma.mul_comm

@[to_additive]

Depends on / 依赖: CommMagma, CommMagma.mul_comm, mul_comm
-/
theorem mul_comm : forall a b : G, a * b = b * a := CommMagma.mul_comm

@[to_additive]
/--
Instance `CommMagma.to_isCommutative` / 实例 `CommMagma.to_isCommutative`

English:
instance CommMagma.to_isCommutative
  signature: : IsMulCommutative G
  body: ⟨⟨mul_comm⟩⟩

@[to_additive (attr := simp)]

中文:
实例 CommMagma.to_isCommutative
  签名: : IsMulCommutative G
  定义体: ⟨⟨mul_comm⟩⟩

@[to_additive (attr := simp)]

Depends on / 依赖: mul_comm
-/
instance CommMagma.to_isCommutative : IsMulCommutative G := ⟨⟨mul_comm⟩⟩

@[to_additive (attr := simp)]
/--
lemma `isLeftRegular_iff_isRegular` / 引理 `isLeftRegular_iff_isRegular`

English:
lemma isLeftRegular_iff_isRegular
  statement: IsLeftRegular a ↔ IsRegular a
  proof: by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

@[to_additive (attr := simp)]

中文:
引理 isLeftRegular_iff_isRegular
  结论: IsLeftRegular a ↔ IsRegular a
  证明: by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

@[to_additive (attr := simp)]

Depends on / 依赖: IsCentralScalar, IsLeftRegular, IsRightRegular, SMulCommClass, SMulCommClass.op_left, isRegular_iff, mul_comm, op_left
-/
lemma isLeftRegular_iff_isRegular : IsLeftRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

@[to_additive (attr := simp)]
/--
lemma `isRightRegular_iff_isRegular` / 引理 `isRightRegular_iff_isRegular`

English:
lemma isRightRegular_iff_isRegular
  statement: IsRightRegular a ↔ IsRegular a
  proof: by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

中文:
引理 isRightRegular_iff_isRegular
  结论: IsRightRegular a ↔ IsRegular a
  证明: by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

Depends on / 依赖: IsLeftRegular, IsRightRegular, SMulCommClass, SMulCommClass.op_right, isRegular_iff, mul_comm, op_right
-/
lemma isRightRegular_iff_isRegular : IsRightRegular a ↔ IsRegular a := by
  simp [isRegular_iff, IsLeftRegular, IsRightRegular, mul_comm]

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsLeftCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsLeftCancelAdd /-- Any `AddCommMagma G` that
satisfies `IsRightCancelAdd G` also satisfies `IsLeftCancelAdd G`. -/]
/--
lemma `CommMagma.IsRightCancelMul.toIsLeftCancelMul` / 引理 `CommMagma.IsRightCancelMul.toIsLeftCancelMul`

English:
lemma CommMagma.IsRightCancelMul.toIsLeftCancelMul
  given: (G : Type u) [CommMagma G] [IsRightCancelMul G]
  proof: ⟨fun _ _ _ h => mul_right_cancel (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

中文:
引理 CommMagma.IsRightCancelMul.toIsLeftCancelMul
  条件: (G : 类型u) [CommMagma G] [IsRightCancelMul G]
  证明: ⟨fun _ _ _ h => mul_right_cancel (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

Depends on / 依赖: IsCentralScalar, IsScalarTower, IsScalarTower.op_left, h.trans, mul_comm, mul_right_cancel, op_left
-/
lemma CommMagma.IsRightCancelMul.toIsLeftCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsLeftCancelMul G :=
⟨fun _ _ _ h => mul_right_cancel (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsRightCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsRightCancelAdd /-- Any `AddCommMagma G` that
satisfies `IsLeftCancelAdd G` also satisfies `IsRightCancelAdd G`. -/]
/--
lemma `CommMagma.IsLeftCancelMul.toIsRightCancelMul` / 引理 `CommMagma.IsLeftCancelMul.toIsRightCancelMul`

English:
lemma CommMagma.IsLeftCancelMul.toIsRightCancelMul
  given: (G : Type u) [CommMagma G] [IsLeftCancelMul G]
  proof: ⟨fun _ _ _ h => mul_left_cancel (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

中文:
引理 CommMagma.IsLeftCancelMul.toIsRightCancelMul
  条件: (G : 类型u) [CommMagma G] [IsLeftCancelMul G]
  证明: ⟨fun _ _ _ h => mul_left_cancel (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

Depends on / 依赖: IsScalarTower, IsScalarTower.op_right, h.trans, mul_comm, mul_left_cancel, op_right
-/
lemma CommMagma.IsLeftCancelMul.toIsRightCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsRightCancelMul G :=
⟨fun _ _ _ h => mul_left_cancel (mul_comm _ _).trans (h.trans (mul_comm _ _))⟩

/-- Any `CommMagma G` that satisfies `IsLeftCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsLeftCancelAdd.toIsCancelAdd /-- Any `AddCommMagma G` that satisfies
`IsLeftCancelAdd G` also satisfies `IsCancelAdd G`. -/]
/--
lemma `CommMagma.IsLeftCancelMul.toIsCancelMul` / 引理 `CommMagma.IsLeftCancelMul.toIsCancelMul`

English:
lemma CommMagma.IsLeftCancelMul.toIsCancelMul
  given: (G : Type u) [CommMagma G] [IsLeftCancelMul G]
  proof: { CommMagma.IsLeftCancelMul.toIsRightCancelMul G with }

中文:
引理 CommMagma.IsLeftCancelMul.toIsCancelMul
  条件: (G : 类型u) [CommMagma G] [IsLeftCancelMul G]
  证明: { CommMagma.IsLeftCancelMul.toIsRightCancelMul G with }

Depends on / 依赖: CommMagma, CommMagma.IsLeftCancelMul.toIsRightCancelMul, IsLeftCancelMul, toIsRightCancelMul
-/
lemma CommMagma.IsLeftCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsLeftCancelMul G] :
    IsCancelMul G := { CommMagma.IsLeftCancelMul.toIsRightCancelMul G with }

/-- Any `CommMagma G` that satisfies `IsRightCancelMul G` also satisfies `IsCancelMul G`. -/
@[to_additive AddCommMagma.IsRightCancelAdd.toIsCancelAdd /-- Any `AddCommMagma G` that satisfies
`IsRightCancelAdd G` also satisfies `IsCancelAdd G`. -/]
/--
lemma `CommMagma.IsRightCancelMul.toIsCancelMul` / 引理 `CommMagma.IsRightCancelMul.toIsCancelMul`

English:
lemma CommMagma.IsRightCancelMul.toIsCancelMul
  given: (G : Type u) [CommMagma G] [IsRightCancelMul G]
  proof: { CommMagma.IsRightCancelMul.toIsLeftCancelMul G with }

中文:
引理 CommMagma.IsRightCancelMul.toIsCancelMul
  条件: (G : 类型u) [CommMagma G] [IsRightCancelMul G]
  证明: { CommMagma.IsRightCancelMul.toIsLeftCancelMul G with }

Depends on / 依赖: CommMagma, CommMagma.IsRightCancelMul.toIsLeftCancelMul, IsRightCancelMul, toIsLeftCancelMul
-/
lemma CommMagma.IsRightCancelMul.toIsCancelMul (G : Type u) [CommMagma G] [IsRightCancelMul G] :
    IsCancelMul G := { CommMagma.IsRightCancelMul.toIsLeftCancelMul G with }

end CommMagma

/-- A `LeftCancelSemigroup` is a semigroup such that `a * b = a * c` implies `b = c`. -/
@[ext]
/--
Definition of `LeftCancelSemigroup` / `LeftCancelSemigroup` 的定义

English:
class LeftCancelSemigroup
  parameters: (G : Type u)
  extends: Semigroup G, IsLeftCancelMul G
  (no additional axioms)

中文:
类 LeftCancelSemigroup
  参数: (G : 类型u)
  继承: Semigroup G, IsLeftCancelMul G
  (无附加公理)
-/
class LeftCancelSemigroup (G : Type u) extends Semigroup G, IsLeftCancelMul G

library_note «lower cancel priority» /--
We lower the priority of inheriting from cancellative structures.
This attempts to avoid expensive checks involving bundling and unbundling with the `IsDomain` class.
since `IsDomain` already depends on `Semiring`, we can synthesize that one first.
Zulip discussion: https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Why.20is.20.60simpNF.60.20complaining.20here.3F
-/
attribute [instance 75] LeftCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddLeftCancelSemigroup` is an additive semigroup such that
`a + b = a + c` implies `b = c`. -/
@[ext]
/--
Definition of `AddLeftCancelSemigroup` / `AddLeftCancelSemigroup` 的定义

English:
class AddLeftCancelSemigroup
  parameters: (G : Type u)
  extends: AddSemigroup G, IsLeftCancelAdd G
  (no additional axioms)

中文:
类 AddLeftCancelSemigroup
  参数: (G : 类型u)
  继承: AddSemigroup G, IsLeftCancelAdd G
  (无附加公理)
-/
class AddLeftCancelSemigroup (G : Type u) extends AddSemigroup G, IsLeftCancelAdd G

attribute [instance 75] AddLeftCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] LeftCancelSemigroup

/-- Any `LeftCancelSemigroup` satisfies `IsLeftCancelMul`. -/
add_decl_doc LeftCancelSemigroup.toIsLeftCancelMul

/-- Any `AddLeftCancelSemigroup` satisfies `IsLeftCancelAdd`. -/
add_decl_doc AddLeftCancelSemigroup.toIsLeftCancelAdd

/-- A `RightCancelSemigroup` is a semigroup such that `a * b = c * b` implies `a = c`. -/
@[ext]
/--
Definition of `RightCancelSemigroup` / `RightCancelSemigroup` 的定义

English:
class RightCancelSemigroup
  parameters: (G : Type u)
  extends: Semigroup G, IsRightCancelMul G
  (no additional axioms)

中文:
类 RightCancelSemigroup
  参数: (G : 类型u)
  继承: Semigroup G, IsRightCancelMul G
  (无附加公理)
-/
class RightCancelSemigroup (G : Type u) extends Semigroup G, IsRightCancelMul G

attribute [instance 75] RightCancelSemigroup.toSemigroup -- See note [lower cancel priority]

/-- An `AddRightCancelSemigroup` is an additive semigroup such that
`a + b = c + b` implies `a = c`. -/
@[ext]
/--
Definition of `AddRightCancelSemigroup` / `AddRightCancelSemigroup` 的定义

English:
class AddRightCancelSemigroup
  parameters: (G : Type u)
  extends: AddSemigroup G, IsRightCancelAdd G
  (no additional axioms)

中文:
类 AddRightCancelSemigroup
  参数: (G : 类型u)
  继承: AddSemigroup G, IsRightCancelAdd G
  (无附加公理)
-/
class AddRightCancelSemigroup (G : Type u) extends AddSemigroup G, IsRightCancelAdd G

attribute [instance 75] AddRightCancelSemigroup.toAddSemigroup -- See note [lower cancel priority]

attribute [to_additive] RightCancelSemigroup

/-- Any `RightCancelSemigroup` satisfies `IsRightCancelMul`. -/
add_decl_doc RightCancelSemigroup.toIsRightCancelMul

/-- Any `AddRightCancelSemigroup` satisfies `IsRightCancelAdd`. -/
add_decl_doc AddRightCancelSemigroup.toIsRightCancelAdd

/--
Definition of `AddZero` / `AddZero` 的定义

English:
class AddZero
  parameters: (M : Type*)
  extends: Zero M, Add M
  (no additional axioms)

中文:
类 AddZero
  参数: (M : 类型)
  继承: Zero M, Add M
  (无附加公理)
-/
class AddZero (M : Type*) extends Zero M, Add M

/-- Bundling a `Mul` and `One` structure together without any axioms about their
compatibility. See `MulOneClass` for the additional assumption that 1 is an identity. -/
@[to_additive (attr := ext)]
/--
Definition of `MulOne` / `MulOne` 的定义

English:
class MulOne
  parameters: (M : Type*)
  extends: One M, Mul M
  (no additional axioms)

中文:
类 MulOne
  参数: (M : 类型)
  继承: One M, Mul M
  (无附加公理)
-/
class MulOne (M : Type*) extends One M, Mul M

/--
Definition of `IsDedekindFiniteAddMonoid` / `IsDedekindFiniteAddMonoid` 的定义

English:
class IsDedekindFiniteAddMonoid
  parameters: (M : Type*) [AddZero M]
  axioms and operations (1):
    - add_eq_zero_symm({a b : M}) : a + b = 0 -> b + a = 0

中文:
类 IsDedekindFiniteAddMonoid
  参数: (M : 类型) [AddZero M]
  公理与运算 (1 个):
    - add_eq_zero_symm({a b : M}) : a + b = 0 -> b + a = 0
-/
class IsDedekindFiniteAddMonoid (M : Type*) [AddZero M] : Prop where
  add_eq_zero_symm {a b : M} : a + b = 0 -> b + a = 0

/--
Definition of `IsDedekindFiniteMonoid` / `IsDedekindFiniteMonoid` 的定义

English:
class IsDedekindFiniteMonoid
  parameters: (M : Type*) [MulOne M]
  axioms and operations (1):
    - mul_eq_one_symm({a b : M}) : a * b = 1 -> b * a = 1

中文:
类 IsDedekindFiniteMonoid
  参数: (M : 类型) [MulOne M]
  公理与运算 (1 个):
    - mul_eq_one_symm({a b : M}) : a * b = 1 -> b * a = 1
-/
@[to_additive (attr := mk_iff)] class IsDedekindFiniteMonoid (M : Type*) [MulOne M] : Prop where
  mul_eq_one_symm {a b : M} : a * b = 1 -> b * a = 1

export IsDedekindFiniteMonoid (mul_eq_one_symm)
export IsDedekindFiniteAddMonoid (add_eq_zero_symm)
attribute [to_additive existing] isDedekindFiniteMonoid_iff

/--
theorem `mul_eq_one_comm` / 定理 `mul_eq_one_comm`

English:
theorem mul_eq_one_comm
  given: {M} [MulOne M] [IsDedekindFiniteMonoid M] {a b : M}
  proof: mul_eq_one_symm
  mpr := mul_eq_one_symm

中文:
定理 mul_eq_one_comm
  条件: {M} [MulOne M] [IsDedekindFiniteMonoid M] {a b : M}
  证明: mul_eq_one_symm
  mpr := mul_eq_one_symm
-/
@[to_additive] theorem mul_eq_one_comm {M} [MulOne M] [IsDedekindFiniteMonoid M] {a b : M} :
    a * b = 1 ↔ b * a = 1 where
  mp := mul_eq_one_symm
  mpr := mul_eq_one_symm

@[to_additive] instance (priority := low) (M) [MulOne M] [IsMulCommutative M] :
    IsDedekindFiniteMonoid M where
.trans mul_eq_one_symm := mul_comm' ..

/--
Definition of `AddZeroClass` / `AddZeroClass` 的定义

English:
class AddZeroClass
  parameters: (M : Type u)
  extends: AddZero M
  axioms and operations (2):
    - zero_add : forall a : M, 0 + a = a
    - add_zero : forall a : M, a + 0 = a

中文:
类 AddZeroClass
  参数: (M : 类型u)
  继承: AddZero M
  公理与运算 (2 个):
    - zero_add : 对任意 a : M, 0 + a = a
    - add_zero : 对任意 a : M, a + 0 = a
-/
class AddZeroClass (M : Type u) extends AddZero M where
  /-- Zero is a left neutral element for addition -/
  protected zero_add : forall a : M, 0 + a = a
  /-- Zero is a right neutral element for addition -/
  protected add_zero : forall a : M, a + 0 = a

/-- Typeclass for expressing that a type `M` with multiplication and a one satisfies
`1 * a = a` and `a * 1 = a` for all `a : M`. -/
@[to_additive]
/--
Definition of `MulOneClass` / `MulOneClass` 的定义

English:
class MulOneClass
  parameters: (M : Type u)
  extends: MulOne M
  axioms and operations (2):
    - one_mul : forall a : M, 1 * a = a
    - mul_one : forall a : M, a * 1 = a

中文:
类 MulOneClass
  参数: (M : 类型u)
  继承: MulOne M
  公理与运算 (2 个):
    - one_mul : 对任意 a : M, 1 * a = a
    - mul_one : 对任意 a : M, a * 1 = a
-/
class MulOneClass (M : Type u) extends MulOne M where
  /-- One is a left neutral element for multiplication -/
  protected one_mul : forall a : M, 1 * a = a
  /-- One is a right neutral element for multiplication -/
  protected mul_one : forall a : M, a * 1 = a

@[to_additive (attr := ext)]
/--
theorem `MulOneClass.ext` / 定理 `MulOneClass.ext`

English:
theorem MulOneClass.ext
  given: {M : Type u}
  statement: forall ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul -> m₁ = m₂
  proof: by
  rintro @⟨@⟨⟨one₁⟩, ⟨mul₁⟩⟩, one_mul₁, mul_one₁⟩ @⟨@⟨⟨one₂⟩, ⟨mul₂⟩⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  -- FIXME (See https://github.com/leanprover/lean4/issues/1711)
  -- congr
  suffices one₁ = one₂ by cases this; rfl
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)

中文:
定理 MulOneClass.ext
  条件: {M : 类型u}
  结论: 对任意 ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul -> m₁ = m₂
  证明: by
  rintro @⟨@⟨⟨one₁⟩, ⟨mul₁⟩⟩, one_mul₁, mul_one₁⟩ @⟨@⟨⟨one₂⟩, ⟨mul₂⟩⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  -- FIXME (See https://github.com/leanprover/lean4/issues/1711)
  -- congr
  suffices one₁ = one₂ by cases this; rfl
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)
-/
theorem MulOneClass.ext {M : Type u} : forall ⦃m₁ m₂ : MulOneClass M⦄, m₁.mul = m₂.mul -> m₁ = m₂ := by
  rintro @⟨@⟨⟨one₁⟩, ⟨mul₁⟩⟩, one_mul₁, mul_one₁⟩ @⟨@⟨⟨one₂⟩, ⟨mul₂⟩⟩, one_mul₂, mul_one₂⟩ ⟨rfl⟩
  -- FIXME (See https://github.com/leanprover/lean4/issues/1711)
  -- congr
  suffices one₁ = one₂ by cases this; rfl
  exact (one_mul₂ one₁).symm.trans (mul_one₁ one₂)

section MulOneClass

variable {M : Type u} [MulOneClass M]

@[to_additive (attr := simp)]
/--
theorem `one_mul` / 定理 `one_mul`

English:
theorem one_mul
  statement: forall a : M, 1 * a = a
  proof: MulOneClass.one_mul

@[to_additive (attr := simp)]

中文:
定理 one_mul
  结论: 对任意 a : M, 1 * a = a
  证明: MulOneClass.one_mul

@[to_additive (attr := simp)]

Depends on / 依赖: MulOneClass, MulOneClass.one_mul, one_mul
-/
theorem one_mul : forall a : M, 1 * a = a :=
  MulOneClass.one_mul

@[to_additive (attr := simp)]
/--
theorem `mul_one` / 定理 `mul_one`

English:
theorem mul_one
  statement: forall a : M, a * 1 = a
  proof: MulOneClass.mul_one

中文:
定理 mul_one
  结论: 对任意 a : M, a * 1 = a
  证明: MulOneClass.mul_one

Depends on / 依赖: MulOneClass, MulOneClass.mul_one, mul_one
-/
theorem mul_one : forall a : M, a * 1 = a :=
  MulOneClass.mul_one

end MulOneClass

section

variable {M : Type u}

attribute [to_additive existing] npowRec

variable [One M] [Semigroup M] (m n : Nat) (hn : n != 0) (a : M) (ha : 1 * a = a)
include hn ha

/--
theorem `npowRec_add` / 定理 `npowRec_add`

English:
theorem npowRec_add
  statement: npowRec (m + n) a = npowRec m a * npowRec n a
  proof: by
  obtain _ | n := n; · exact (hn rfl).elim
  induction n with
  | zero => simp only [npowRec, ha]
  | succ n ih => rw [← Nat.add_assoc, npowRec, ih n.succ_ne_zero]; simp only [npowRec, mul_assoc]

中文:
定理 npowRec_add
  结论: npowRec (m + n) a = npowRec m a * npowRec n a
  证明: by
  obtain _ | n := n; · exact (hn rfl).elim
  induction n with
  | zero => simp only [npowRec, ha]
  | succ n ih => rw [← Nat.add_assoc, npowRec, ih n.succ_ne_zero]; simp only [npowRec, mul_assoc]
-/
@[to_additive] theorem npowRec_add : npowRec (m + n) a = npowRec m a * npowRec n a := by
  obtain _ | n := n; · exact (hn rfl).elim
  induction n with
  | zero => simp only [npowRec, ha]
  | succ n ih => rw [← Nat.add_assoc, npowRec, ih n.succ_ne_zero]; simp only [npowRec, mul_assoc]

/--
theorem `npowRec_succ` / 定理 `npowRec_succ`

English:
theorem npowRec_succ
  statement: npowRec (n + 1) a = a * npowRec n a
  proof: by
  rw [Nat.add_comm]; rw [npowRec_add 1 n hn a ha]; rw [npowRec]; rw [npowRec]; rw [ha]

中文:
定理 npowRec_succ
  结论: npowRec (n + 1) a = a * npowRec n a
  证明: by
  rw [Nat.add_comm]; rw [npowRec_add 1 n hn a ha]; rw [npowRec]; rw [npowRec]; rw [ha]
-/
@[to_additive] theorem npowRec_succ : npowRec (n + 1) a = a * npowRec n a := by
  rw [Nat.add_comm]; rw [npowRec_add 1 n hn a ha]; rw [npowRec]; rw [npowRec]; rw [ha]

end

library_note «forgetful inheritance» /--
Suppose that one can put two mathematical structures on a type, a rich one `R` and a poor one
`P`, and that one can deduce the poor structure from the rich structure through a map `F` (called a
forgetful functor) (think `R = MetricSpace` and `P = TopologicalSpace`). A possible
implementation would be to have a type class `rich` containing a field `R`, a type class `poor`
containing a field `P`, and an instance from `rich` to `poor`. However, this creates diamond
problems, and a better approach is to let `rich` extend `poor` and have a field saying that
`F R = P`.

To illustrate this, consider the pair `MetricSpace` / `TopologicalSpace`. Consider the topology
on a product of two metric spaces. With the first approach, it could be obtained by going first from
each metric space to its topology, and then taking the product topology. But it could also be
obtained by considering the product metric space (with its sup distance) and then the topology
coming from this distance. These would be the same topology, but not definitionally, which means
that from the point of view of Lean's kernel, there would be two different `TopologicalSpace`
instances on the product. This is not compatible with the way instances are designed and used:
there should be at most one instance of a kind on each type. This approach has created an instance
diamond that does not commute definitionally.

The second approach solves this issue. Now, a metric space contains both a distance, a topology, and
a proof that the topology coincides with the one coming from the distance. When one defines the
product of two metric spaces, one uses the sup distance and the product topology, and one has to
give the proof that the sup distance induces the product topology. Following both sides of the
/--
Instance `diamond` / 实例 `diamond`

English:
instance diamond
  signature: then gives rise (definitionally) to the product topology on the product space.

中文:
实例 diamond
  签名: then gives rise (definitionally) to the product topology on the product space.
-/
instance diamond then gives rise (definitionally) to the product topology on the product space.

Another approach would be to have the rich type class take the poor type class as an instance
parameter. It would solve the diamond problem, but it would lead to a blow up of the number
of type classes one would need to declare to work with complicated classes, say a real inner
product space, and would create exponential complexity when working with products of
such complicated spaces, that are avoided by bundling things carefully as above.

Note that this description of this specific case of the product of metric spaces is oversimplified
compared to mathlib, as there is an intermediate typeclass between `MetricSpace` and
`TopologicalSpace` called `UniformSpace`. The above scheme is used at both levels, embedding a
topology in the uniform space structure, and a uniform structure in the metric space structure.

Note also that, when `P` is a proposition, there is no such issue as any two proofs of `P` are
definitionally equivalent in Lean.

To avoid boilerplate, there are some designs that can automatically fill the poor fields when
creating a rich structure if one doesn't want to do something special about them. For instance,
in the definition of metric spaces, default tactics fill the uniform space fields if they are
not given explicitly. One can also have a helper function creating the rich structure from a
/--
Definition of `with` / `with` 的定义

English:
structure with
  parameters: fewer fields,
  (no additional axioms)

中文:
结构 with
  参数: fewer fields,
  (无附加公理)
-/
structure with fewer fields, where the helper function fills the remaining fields. See for instance
`UniformSpace.ofCore` or `RealInnerProduct.ofCore`.

For more details on this question, called the forgetful inheritance pattern, see [Competing
inheritance paths in dependent type theory: a case study in functional
analysis](https://hal.inria.fr/hal-02463336).
-/


/-!
### Design note on `AddMonoid` and `Monoid`

An `AddMonoid` has a natural `ℕ`-action, defined by `n • a = a + ... + a`, that we want to declare
as an instance as it makes it possible to use the language of linear algebra. However, there are
often other natural `ℕ`-actions. For instance, for any semiring `R`, the space of polynomials
`Polynomial R` has a natural `R`-action defined by multiplication on the coefficients. This means
that `Polynomial ℕ` would have two natural `ℕ`-actions, which are equal but not defeq. The same
goes for linear maps, tensor products, and so on (and even for `ℕ` itself).

To solve this issue, we embed an `ℕ`-action in the definition of an `AddMonoid` (which is by
default equal to the naive action `a + ... + a`, but can be adjusted when needed), and declare
a `SMul ℕ α` instance using this action. See Note [forgetful inheritance] for more
explanations on this pattern.

For example, when we define `Polynomial R`, then we declare the `ℕ`-action to be by multiplication
on each coefficient (using the `ℕ`-action on `R` that comes from the fact that `R` is
an `AddMonoid`). In this way, the two natural `SMul ℕ (Polynomial ℕ)` instances are defeq.

The tactic `to_additive` transfers definitions and results from multiplicative monoids to additive
monoids. To work, it has to map fields to fields. This means that we should also add corresponding
fields to the multiplicative structure `Monoid`, which could solve defeq problems for powers if
needed. These problems do not come up in practice, so most of the time we will not need to adjust
the `npow` field when defining multiplicative objects.
-/

/-- Exponentiation by repeated squaring. -/
@[to_additive /-- Scalar multiplication by repeated self-addition,
the additive version of exponentiation by repeated squaring. -/]
/--
Definition of `npowBinRec` / `npowBinRec` 的定义

English:
definition npowBinRec
  signature: {M : Type*} [One M] [Mul M] (k : Nat)
  body: npowBinRec.go k 1

中文:
定义 npowBinRec
  签名: {M : 类型} [One M] [Mul M] (k : 自然数)
  定义体: npowBinRec.go k 1

Depends on / 依赖: Monoid, Monoid.toMulAction, MulAction, npowBinRec, npowBinRec.go, toMulAction
-/
def npowBinRec {M : Type*} [One M] [Mul M] (k : Nat) : M -> M :=
  npowBinRec.go k 1
where
  /-- Auxiliary tail-recursive implementation for `npowBinRec`. -/
  @[to_additive nsmulBinRec.go /-- Auxiliary tail-recursive implementation for `nsmulBinRec`. -/]
  go (k : Nat) : M -> M -> M :=
    k.binaryRec (fun y _ => y) fun bn _n fn y x => fn (cond bn (y * x) y) (x * x)

/--
Definition of `npowRec'` / `npowRec'` 的定义

English:
definition npowRec'
  signature: {M : Type*} [One M] [Mul M]

中文:
定义 npowRec'
  签名: {M : 类型} [One M] [Mul M]
-/
def npowRec' {M : Type*} [One M] [Mul M] : Nat -> M -> M
  | 0, _ => 1
  | 1, m => m
  | k + 2, m => npowRec' (k + 1) m * m

/--
Definition of `nsmulRec'` / `nsmulRec'` 的定义

English:
definition nsmulRec'
  signature: {M : Type*} [Zero M] [Add M]

中文:
定义 nsmulRec'
  签名: {M : 类型} [Zero M] [Add M]

Depends on / 依赖: one_smul, smul_assoc, smul_comm
-/
def nsmulRec' {M : Type*} [Zero M] [Add M] : Nat -> M -> M
  | 0, _ => 0
  | 1, m => m
  | k + 2, m => nsmulRec' (k + 1) m + m

attribute [to_additive existing] npowRec'

@[to_additive]
/--
theorem `npowRec'_succ` / 定理 `npowRec'_succ`

English:
theorem npowRec'_succ
  given: {M : Type*} [Mul M] [One M] {k : Nat} (_ : k != 0) (m : M)
  proof: match k with
  | _ + 1 => rfl

@[to_additive]

中文:
定理 npowRec'_succ
  条件: {M : 类型} [Mul M] [One M] {k : 自然数} (_ : k != 0) (m : M)
  证明: match k with
  | _ + 1 => rfl

@[to_additive]
-/
theorem npowRec'_succ {M : Type*} [Mul M] [One M] {k : Nat} (_ : k != 0) (m : M) :
    npowRec' (k + 1) m = npowRec' k m * m :=
  match k with
  | _ + 1 => rfl

@[to_additive]
/--
theorem `npowRec'_two_mul` / 定理 `npowRec'_two_mul`

English:
theorem npowRec'_two_mul
  given: {M : Type*} [Semigroup M] [One M] (k : Nat) (m : M)
  proof: by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | 1 => simp [npowRec']
    | k + 2 =>
      simp [npowRec', ← mul_assoc, ← ih, Nat.mul_succ]

@[to_additive]

中文:
定理 npowRec'_two_mul
  条件: {M : 类型} [Semigroup M] [One M] (k : 自然数) (m : M)
  证明: by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | 1 => simp [npowRec']
    | k + 2 =>
      simp [npowRec', ← mul_assoc, ← ih, Nat.mul_succ]

@[to_additive]
-/
theorem npowRec'_two_mul {M : Type*} [Semigroup M] [One M] (k : Nat) (m : M) :
    npowRec' (2 * k) m = npowRec' k (m * m) := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | 1 => simp [npowRec']
    | k + 2 =>
      simp [npowRec', ← mul_assoc, ← ih, Nat.mul_succ]

@[to_additive]
/--
theorem `npowRec'_mul_comm` / 定理 `npowRec'_mul_comm`

English:
theorem npowRec'_mul_comm
  given: {M : Type*} [Semigroup M] [One M] {k : Nat} (k0 : k != 0) (m : M)
  proof: by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ih]

@[to_additive]

中文:
定理 npowRec'_mul_comm
  条件: {M : 类型} [Semigroup M] [One M] {k : 自然数} (k0 : k != 0) (m : M)
  证明: by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ih]

@[to_additive]
-/
theorem npowRec'_mul_comm {M : Type*} [Semigroup M] [One M] {k : Nat} (k0 : k != 0) (m : M) :
    m * npowRec' k m = npowRec' k m * m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 1 => simp [npowRec']
    | k + 2 => simp [npowRec', ← mul_assoc, ih]

@[to_additive]
/--
theorem `npowRec_eq` / 定理 `npowRec_eq`

English:
theorem npowRec_eq
  given: {M : Type*} [Semigroup M] [One M] (k : Nat) (m : M)
  proof: by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | k + 1 =>
      rw [npowRec]; rw [npowRec'_succ k.succ_ne_zero]; rw [← mul_assoc]
      congr
      simp [ih]

@[to_additive]

中文:
定理 npowRec_eq
  条件: {M : 类型} [Semigroup M] [One M] (k : 自然数) (m : M)
  证明: by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | k + 1 =>
      rw [npowRec]; rw [npowRec'_succ k.succ_ne_zero]; rw [← mul_assoc]
      congr
      simp [ih]

@[to_additive]

Depends on / 依赖: Nat.strongRecOn, _succ, k.succ_ne_zero, mul_assoc, npowRec, strongRecOn, succ_ne_zero
-/
theorem npowRec_eq {M : Type*} [Semigroup M] [One M] (k : Nat) (m : M) :
    npowRec (k + 1) m = 1 * npowRec' (k + 1) m := by
  induction k using Nat.strongRecOn with
  | ind k' ih =>
    match k' with
    | 0 => rfl
    | k + 1 =>
      rw [npowRec]; rw [npowRec'_succ k.succ_ne_zero]; rw [← mul_assoc]
      congr
      simp [ih]

@[to_additive]
/--
theorem `npowBinRec.go_spec` / 定理 `npowBinRec.go_spec`

English:
theorem npowBinRec.go_spec
  given: {M : Type*} [Semigroup M] [One M] (k : Nat) (m n : M)
  proof: by
  unfold go
  generalize hk : k + 1 = k'
  replace hk : k' != 0 := by lia
  induction k' using Nat.binaryRecFromOne generalizing n m with
  | zero => simp at hk
  | one => simp [npowRec']
  | bit b k' k'0 ih =>
    rw [Nat.binaryRec_eq _ _ (Or.inl rfl)]; rw [ih _ _ k'0]
    cases b <;> simp only 

中文:
定理 npowBinRec.go_spec
  条件: {M : 类型} [Semigroup M] [One M] (k : 自然数) (m n : M)
  证明: by
  unfold go
  generalize hk : k + 1 = k'
  replace hk : k' != 0 := by lia
  induction k' using Nat.binaryRecFromOne generalizing n m with
  | zero => simp at hk
  | one => simp [npowRec']
  | bit b k' k'0 ih =>
    rw [Nat.binaryRec_eq _ _ (Or.inl rfl)]; rw [ih _ _ k'0]
    cases b <;> simp only 

Depends on / 依赖: Nat.binaryRecFromOne, Nat.binaryRec_eq, Nat.bit, Or.inl, _mul_comm, _succ, _two_mul, binaryRecFromOne, binaryRec_eq, cond_false, cond_true, generalize, generalizing, mul_assoc, npowRec, replace
-/
theorem npowBinRec.go_spec {M : Type*} [Semigroup M] [One M] (k : Nat) (m n : M) :
    npowBinRec.go (k + 1) m n = m * npowRec' (k + 1) n := by
  unfold go
  generalize hk : k + 1 = k'
  replace hk : k' != 0 := by lia
  induction k' using Nat.binaryRecFromOne generalizing n m with
  | zero => simp at hk
  | one => simp [npowRec']
  | bit b k' k'0 ih =>
    rw [Nat.binaryRec_eq _ _ (Or.inl rfl)]; rw [ih _ _ k'0]
    cases b <;> simp only [Nat.bit, cond_false, cond_true, npowRec'_two_mul]
    rw [npowRec'_succ (by lia)]; rw [npowRec'_two_mul]; rw [← npowRec'_two_mul]; rw [← npowRec'_mul_comm (by lia)]; rw [mul_assoc]

/--
An abbreviation for `npowRec` with an additional typeclass assumption on associativity
so that we can use `@[csimp]` to replace it with an implementation by repeated squaring
in compiled code.
-/
@[to_additive
/-- An abbreviation for `nsmulRec` with an additional typeclass assumptions on associativity
so that we can use `@[csimp]` to replace it with an implementation by repeated doubling in compiled
code as an automatic parameter. -/]
/--
Definition of `npowRecAuto` / `npowRecAuto` 的定义

English:
abbreviation npowRecAuto
  signature: {M : Type*} [Semigroup M] [One M] (k : Nat) (m : M)
  body: npowRec k m

中文:
缩写 npowRecAuto
  签名: {M : 类型} [Semigroup M] [One M] (k : 自然数) (m : M)
  定义体: npowRec k m

Depends on / 依赖: npowRec
-/
abbrev npowRecAuto {M : Type*} [Semigroup M] [One M] (k : Nat) (m : M) : M :=
  npowRec k m

/--
An abbreviation for `npowBinRec` with an additional typeclass assumption on associativity
so that we can use it in `@[csimp]` for more performant code generation.
-/
@[to_additive
/-- An abbreviation for `nsmulBinRec` with an additional typeclass assumption on associativity
so that we can use it in `@[csimp]` for more performant code generation
as an automatic parameter. -/]
/--
Definition of `npowBinRecAuto` / `npowBinRecAuto` 的定义

English:
abbreviation npowBinRecAuto
  signature: {M : Type*} [Semigroup M] [One M] (k : Nat) (m : M)
  body: npowBinRec k m

@[to_additive (attr := csimp)]

中文:
缩写 npowBinRecAuto
  签名: {M : 类型} [Semigroup M] [One M] (k : 自然数) (m : M)
  定义体: npowBinRec k m

@[to_additive (attr := csimp)]

Depends on / 依赖: npowBinRec
-/
abbrev npowBinRecAuto {M : Type*} [Semigroup M] [One M] (k : Nat) (m : M) : M :=
  npowBinRec k m

@[to_additive (attr := csimp)]
/--
theorem `npowRec_eq_npowBinRec` / 定理 `npowRec_eq_npowBinRec`

English:
theorem npowRec_eq_npowBinRec
  statement: @npowRecAuto = @npowBinRecAuto
  proof: by
  funext M _ _ k m
  rw [npowBinRecAuto]; rw [npowRecAuto]; rw [npowBinRec]
  match k with
  | 0 => rw [npowRec, npowBinRec.go, Nat.binaryRec_zero]
  | k + 1 => rw [npowBinRec.go_spec, npowRec_eq]

中文:
定理 npowRec_eq_npowBinRec
  结论: @npowRecAuto = @npowBinRecAuto
  证明: by
  funext M _ _ k m
  rw [npowBinRecAuto]; rw [npowRecAuto]; rw [npowBinRec]
  match k with
  | 0 => rw [npowRec, npowBinRec.go, Nat.binaryRec_zero]
  | k + 1 => rw [npowBinRec.go_spec, npowRec_eq]

Depends on / 依赖: Nat.binaryRec_zero, binaryRec_zero, go_spec, npowBinRec, npowBinRec.go, npowBinRec.go_spec, npowBinRecAuto, npowRec, npowRecAuto, npowRec_eq
-/
theorem npowRec_eq_npowBinRec : @npowRecAuto = @npowBinRecAuto := by
  funext M _ _ k m
  rw [npowBinRecAuto]; rw [npowRecAuto]; rw [npowBinRec]
  match k with
  | 0 => rw [npowRec, npowBinRec.go, Nat.binaryRec_zero]
  | k + 1 => rw [npowBinRec.go_spec, npowRec_eq]

/--
theorem `npowBinRec_zero` / 定理 `npowBinRec_zero`

English:
theorem npowBinRec_zero
  given: {M : Type*} [Mul M] [One M] (m : M)
  proof: rfl

中文:
定理 npowBinRec_zero
  条件: {M : 类型} [Mul M] [One M] (m : M)
  证明: rfl
-/
@[to_additive] theorem npowBinRec_zero {M : Type*} [Mul M] [One M] (m : M) :
    npowBinRec 0 m = 1 := rfl

/--
theorem `npowBinRec_succ` / 定理 `npowBinRec_succ`

English:
theorem npowBinRec_succ
  given: {M : Type*} [Semigroup M] [One M] (n : Nat) (m : M)
  proof: by
  iterate 2 rw [← npowBinRecAuto, ← npowRec_eq_npowBinRec]
  rfl

中文:
定理 npowBinRec_succ
  条件: {M : 类型} [Semigroup M] [One M] (n : 自然数) (m : M)
  证明: by
  iterate 2 rw [← npowBinRecAuto, ← npowRec_eq_npowBinRec]
  rfl
-/
@[to_additive] theorem npowBinRec_succ {M : Type*} [Semigroup M] [One M] (n : Nat) (m : M) :
    npowBinRec (n + 1) m = npowBinRec n m * m := by
  iterate 2 rw [← npowBinRecAuto, ← npowRec_eq_npowBinRec]
  rfl

/--
Definition of `NSMul` / `NSMul` 的定义

English:
class NSMul
  parameters: (M : Type u)
  axioms and operations (1):
    - nsmul : Nat -> M -> M

中文:
类 NSMul
  参数: (M : 类型u)
  公理与运算 (1 个):
    - nsmul : 自然数 -> M -> M
-/
class NSMul (M : Type u) where
  /-- Multiplication by a natural number.
  Set this to `nsmulRec` unless `Module` diamonds are possible. -/
  protected nsmul : Nat -> M -> M

/-- `NPow` is an implementation detail of `Monoid`. It is needed because it is
impossible to extend `Pow M ℕ` and `Pow M ℤ` at the same time. -/
@[to_additive]
/--
Definition of `NPow` / `NPow` 的定义

English:
class NPow
  parameters: (M : Type u)
  axioms and operations (1):
    - npow : Nat -> M -> M

中文:
类 NPow
  参数: (M : 类型u)
  公理与运算 (1 个):
    - npow : 自然数 -> M -> M
-/
class NPow (M : Type u) where
  /-- Raising to the power of a natural number. -/
  protected npow : Nat -> M -> M

@[default_instance high, to_additive toSMul]
/--
Instance `NPow.toPow` / 实例 `NPow.toPow`

English:
instance NPow.toPow
  signature: {M : Type*} [NPow M]
  body: ⟨fun x n => NPow.npow n x⟩

@[to_additive ofSMul]

中文:
实例 NPow.toPow
  签名: {M : 类型} [NPow M]
  定义体: ⟨fun x n => NPow.npow n x⟩

@[to_additive ofSMul]

Depends on / 依赖: NPow.npow
-/
instance NPow.toPow {M : Type*} [NPow M] : Pow M Nat :=
  ⟨fun x n => NPow.npow n x⟩

@[to_additive ofSMul]
/--
Instance `NPow.ofPow` / 实例 `NPow.ofPow`

English:
instance NPow.ofPow
  signature: {M : Type*} [Pow M Nat]
  body: ⟨fun n x => Pow.pow x n⟩

中文:
实例 NPow.ofPow
  签名: {M : 类型} [Pow M 自然数]
  定义体: ⟨fun n x => Pow.pow x n⟩

Depends on / 依赖: Pow.pow
-/
instance NPow.ofPow {M : Type*} [Pow M Nat] : NPow M := ⟨fun n x => Pow.pow x n⟩

/--
Definition of `AddMonoid` / `AddMonoid` 的定义

English:
class AddMonoid
  parameters: (M : Type u)
  extends: AddSemigroup M, AddZeroClass M, NSMul M
  axioms and operations (2):
    - nsmul_zero((x : M)) : 0 • x = 0  [default: by intros; rfl]
    - nsmul_succ((n : Nat) (x : M)) : (n + 1) • x = n • x + x  [default: by intros; rfl]

中文:
类 AddMonoid
  参数: (M : 类型u)
  继承: AddSemigroup M, AddZeroClass M, NSMul M
  公理与运算 (2 个):
    - nsmul_zero((x : M)) : 0 • x = 0  [默认: by intros; rfl]
    - nsmul_succ((n : 自然数) (x : M)) : (n + 1) • x = n • x + x  [默认: by intros; rfl]

Depends on / 依赖: intros
-/
class AddMonoid (M : Type u) extends AddSemigroup M, AddZeroClass M, NSMul M where
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  protected nsmul_zero (x : M) : 0 • x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  protected nsmul_succ (n : Nat) (x : M) : (n + 1) • x = n • x + x := by intros; rfl

attribute [instance 150] AddSemigroup.toAdd
attribute [instance 50] AddZero.toAdd

/-- A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`. -/
@[to_additive]
/--
Definition of `Monoid` / `Monoid` 的定义

English:
class Monoid
  parameters: (M : Type u)
  extends: Semigroup M, MulOneClass M, NPow M
  axioms and operations (3):
    - npow : = npowRecAuto
    - npow_zero((x : M)) : x ^ 0 = 1  [default: by intros; rfl]
    - npow_succ((n : Nat) (x : M)) : x ^ (n + 1) = x ^ n * x  [default: by intros; rfl]

中文:
类 Monoid
  参数: (M : 类型u)
  继承: Semigroup M, MulOneClass M, NPow M
  公理与运算 (3 个):
    - npow : = npowRecAuto
    - npow_zero((x : M)) : x ^ 0 = 1  [默认: by intros; rfl]
    - npow_succ((n : 自然数) (x : M)) : x ^ (n + 1) = x ^ n * x  [默认: by intros; rfl]

Depends on / 依赖: npowRecAuto
-/
class Monoid (M : Type u) extends Semigroup M, MulOneClass M, NPow M where
  npow := npowRecAuto
  /-- Raising to the power `(0 : ℕ)` gives `1`. -/
  protected npow_zero (x : M) : x ^ 0 = 1 := by intros; rfl
  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/
  protected npow_succ (n : Nat) (x : M) : x ^ (n + 1) = x ^ n * x := by intros; rfl

section Monoid
variable {M : Type*} [Monoid M] {a b c : M}

@[to_additive (attr := simp) nsmul_eq_smul]
/--
theorem `npow_eq_pow` / 定理 `npow_eq_pow`

English:
theorem npow_eq_pow
  given: (n : Nat) (x : M)
  statement: NPow.npow n x = x ^ n
  proof: rfl

中文:
定理 npow_eq_pow
  条件: (n : 自然数) (x : M)
  结论: NPow.npow n x = x ^ n
  证明: rfl
-/
theorem npow_eq_pow (n : Nat) (x : M) : NPow.npow n x = x ^ n :=
  rfl

/--
lemma `left_inv_eq_right_inv` / 引理 `left_inv_eq_right_inv`

English:
lemma left_inv_eq_right_inv
  given: (hba : b * a = 1) (hac : a * c = 1)
  statement: b = c
  proof: by
  rw [← one_mul c]; rw [← hba]; rw [mul_assoc]; rw [hac]; rw [mul_one b]

中文:
引理 left_inv_eq_right_inv
  条件: (hba : b * a = 1) (hac : a * c = 1)
  结论: b = c
  证明: by
  rw [← one_mul c]; rw [← hba]; rw [mul_assoc]; rw [hac]; rw [mul_one b]
-/
@[to_additive] lemma left_inv_eq_right_inv (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c]; rw [← hba]; rw [mul_assoc]; rw [hac]; rw [mul_one b]

-- This lemma is higher priority than later `zero_smul` so that the `simpNF` is happy
@[to_additive (attr := simp high) zero_nsmul]
/--
theorem `pow_zero` / 定理 `pow_zero`

English:
theorem pow_zero
  given: (a : M)
  statement: a ^ 0 = 1
  proof: Monoid.npow_zero _

@[to_additive succ_nsmul]

中文:
定理 pow_zero
  条件: (a : M)
  结论: a ^ 0 = 1
  证明: Monoid.npow_zero _

@[to_additive succ_nsmul]

Depends on / 依赖: Monoid, Monoid.npow_zero, npow_zero
-/
theorem pow_zero (a : M) : a ^ 0 = 1 :=
  Monoid.npow_zero _

@[to_additive succ_nsmul]
/--
theorem `pow_succ` / 定理 `pow_succ`

English:
theorem pow_succ
  given: (a : M) (n : Nat)
  statement: a ^ (n + 1) = a ^ n * a
  proof: Monoid.npow_succ n a

@[to_additive one_nsmul, simp]

中文:
定理 pow_succ
  条件: (a : M) (n : 自然数)
  结论: a ^ (n + 1) = a ^ n * a
  证明: Monoid.npow_succ n a

@[to_additive one_nsmul, simp]

Depends on / 依赖: Monoid, Monoid.npow_succ, npow_succ
-/
theorem pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a :=
  Monoid.npow_succ n a

@[to_additive one_nsmul, simp]
/--
lemma `pow_one` / 引理 `pow_one`

English:
lemma pow_one
  given: (a : M)
  statement: a ^ 1 = a
  proof: by rw [pow_succ, pow_zero, one_mul]

中文:
引理 pow_one
  条件: (a : M)
  结论: a ^ 1 = a
  证明: by rw [pow_succ, pow_zero, one_mul]

Depends on / 依赖: one_mul, pow_succ, pow_zero
-/
lemma pow_one (a : M) : a ^ 1 = a := by rw [pow_succ, pow_zero, one_mul]

/--
lemma `pow_succ'` / 引理 `pow_succ'`

English:
lemma pow_succ'
  given: (a : M)
  statement: forall n, a ^ (n + 1) = a * a ^ n

中文:
引理 pow_succ'
  条件: (a : M)
  结论: 对任意 n, a ^ (n + 1) = a * a ^ n
-/
@[to_additive succ_nsmul'] lemma pow_succ' (a : M) : forall n, a ^ (n + 1) = a * a ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ _ n, pow_succ, pow_succ', mul_assoc]

/--
lemma `mul_pow_mul` / 引理 `mul_pow_mul`

English:
lemma mul_pow_mul
  given: (a b : M) (n : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ← ih, mul_assoc]

@[to_additive]

中文:
引理 mul_pow_mul
  条件: (a b : M) (n : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ← ih, mul_assoc]

@[to_additive]
-/
@[to_additive] lemma mul_pow_mul (a b : M) (n : Nat) :
    (a * b) ^ n * a = a * (b * a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ', ← ih, mul_assoc]

@[to_additive]
/--
lemma `pow_mul_comm'` / 引理 `pow_mul_comm'`

English:
lemma pow_mul_comm'
  given: (a : M) (n : Nat)
  statement: a ^ n * a = a * a ^ n
  proof: by rw [← pow_succ, pow_succ']

中文:
引理 pow_mul_comm'
  条件: (a : M) (n : 自然数)
  结论: a ^ n * a = a * a ^ n
  证明: by rw [← pow_succ, pow_succ']

Depends on / 依赖: pow_succ
-/
lemma pow_mul_comm' (a : M) (n : Nat) : a ^ n * a = a * a ^ n := by rw [← pow_succ, pow_succ']

/--
lemma `pow_two` / 引理 `pow_two`

English:
lemma pow_two
  given: (a : M)
  statement: a ^ 2 = a * a
  proof: by rw [pow_succ, pow_one]

中文:
引理 pow_two
  条件: (a : M)
  结论: a ^ 2 = a * a
  证明: by rw [pow_succ, pow_one]
-/
@[to_additive two_nsmul] lemma pow_two (a : M) : a ^ 2 = a * a := by rw [pow_succ, pow_one]

-- TODO: Should `alias` automatically transfer `to_additive` statements?
@[to_additive existing two_nsmul] alias sq := pow_two

@[to_additive three'_nsmul]
/--
lemma `pow_three'` / 引理 `pow_three'`

English:
lemma pow_three'
  given: (a : M)
  statement: a ^ 3 = a * a * a
  proof: by rw [pow_succ, pow_two]

@[to_additive three_nsmul]

中文:
引理 pow_three'
  条件: (a : M)
  结论: a ^ 3 = a * a * a
  证明: by rw [pow_succ, pow_two]

@[to_additive three_nsmul]

Depends on / 依赖: pow_succ, pow_two
-/
lemma pow_three' (a : M) : a ^ 3 = a * a * a := by rw [pow_succ, pow_two]

@[to_additive three_nsmul]
/--
lemma `pow_three` / 引理 `pow_three`

English:
lemma pow_three
  given: (a : M)
  statement: a ^ 3 = a * (a * a)
  proof: by rw [pow_succ', pow_two]

中文:
引理 pow_three
  条件: (a : M)
  结论: a ^ 3 = a * (a * a)
  证明: by rw [pow_succ', pow_two]

Depends on / 依赖: pow_succ, pow_two
-/
lemma pow_three (a : M) : a ^ 3 = a * (a * a) := by rw [pow_succ', pow_two]

-- This lemma is higher priority than later `smul_zero` so that the `simpNF` is happy
/--
lemma `one_pow` / 引理 `one_pow`

English:
lemma one_pow
  statement: forall n, (1 : M) ^ n = 1

中文:
引理 one_pow
  结论: 对任意 n, (1 : M) ^ n = 1
-/
@[to_additive (attr := simp high) nsmul_zero] lemma one_pow : forall n, (1 : M) ^ n = 1
  | 0 => pow_zero _
  | n + 1 => by rw [pow_succ, one_pow, one_mul]

@[to_additive add_nsmul]
/--
lemma `pow_add` / 引理 `pow_add`

English:
lemma pow_add
  given: (a : M) (m : Nat)
  statement: forall n, a ^ (m + n) = a ^ m * a ^ n

中文:
引理 pow_add
  条件: (a : M) (m : 自然数)
  结论: 对任意 n, a ^ (m + n) = a ^ m * a ^ n
-/
lemma pow_add (a : M) (m : Nat) : forall n, a ^ (m + n) = a ^ m * a ^ n
  | 0 => by rw [Nat.add_zero, pow_zero, mul_one]
  | n + 1 => by rw [pow_succ, ← mul_assoc, ← pow_add, ← pow_succ, Nat.add_assoc]

/--
lemma `pow_mul_comm` / 引理 `pow_mul_comm`

English:
lemma pow_mul_comm
  given: (a : M) (m n : Nat)
  statement: a ^ m * a ^ n = a ^ n * a ^ m
  proof: by
  rw [← pow_add]; rw [← pow_add]; rw [Nat.add_comm]

中文:
引理 pow_mul_comm
  条件: (a : M) (m n : 自然数)
  结论: a ^ m * a ^ n = a ^ n * a ^ m
  证明: by
  rw [← pow_add]; rw [← pow_add]; rw [Nat.add_comm]
-/
@[to_additive] lemma pow_mul_comm (a : M) (m n : Nat) : a ^ m * a ^ n = a ^ n * a ^ m := by
  rw [← pow_add]; rw [← pow_add]; rw [Nat.add_comm]

/--
lemma `pow_mul` / 引理 `pow_mul`

English:
lemma pow_mul
  given: (a : M) (m : Nat)
  statement: forall n, a ^ (m * n) = (a ^ m) ^ n

中文:
引理 pow_mul
  条件: (a : M) (m : 自然数)
  结论: 对任意 n, a ^ (m * n) = (a ^ m) ^ n
-/
@[to_additive mul_nsmul] lemma pow_mul (a : M) (m : Nat) : forall n, a ^ (m * n) = (a ^ m) ^ n
  | 0 => by rw [Nat.mul_zero, pow_zero, pow_zero]
  | n + 1 => by rw [Nat.mul_succ, pow_add, pow_succ, pow_mul]

@[to_additive mul_nsmul']
/--
lemma `pow_mul'` / 引理 `pow_mul'`

English:
lemma pow_mul'
  given: (a : M) (m n : Nat)
  statement: a ^ (m * n) = (a ^ n) ^ m
  proof: by rw [Nat.mul_comm, pow_mul]

@[to_additive nsmul_left_comm]

中文:
引理 pow_mul'
  条件: (a : M) (m n : 自然数)
  结论: a ^ (m * n) = (a ^ n) ^ m
  证明: by rw [Nat.mul_comm, pow_mul]

@[to_additive nsmul_left_comm]

Depends on / 依赖: Nat.mul_comm, mul_comm, pow_mul
-/
lemma pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m := by rw [Nat.mul_comm, pow_mul]

@[to_additive nsmul_left_comm]
/--
lemma `pow_right_comm` / 引理 `pow_right_comm`

English:
lemma pow_right_comm
  given: (a : M) (m n : Nat)
  statement: (a ^ m) ^ n = (a ^ n) ^ m
  proof: by
  rw [← pow_mul]; rw [Nat.mul_comm]; rw [pow_mul]

中文:
引理 pow_right_comm
  条件: (a : M) (m n : 自然数)
  结论: (a ^ m) ^ n = (a ^ n) ^ m
  证明: by
  rw [← pow_mul]; rw [Nat.mul_comm]; rw [pow_mul]

Depends on / 依赖: Nat.mul_comm, mul_comm, pow_mul
-/
lemma pow_right_comm (a : M) (m n : Nat) : (a ^ m) ^ n = (a ^ n) ^ m := by
  rw [← pow_mul]; rw [Nat.mul_comm]; rw [pow_mul]

/--
lemma `IsLeftRegular.mul_eq_one_symm` / 引理 `IsLeftRegular.mul_eq_one_symm`

English:
lemma IsLeftRegular.mul_eq_one_symm
  statement: {a b : M} (reg : IsLeftRegular a)
  proof: reg by simp [← mul_assoc, eq]

中文:
引理 IsLeftRegular.mul_eq_one_symm
  结论: {a b : M} (reg : IsLeftRegular a)
  证明: reg by simp [← mul_assoc, eq]
-/
@[to_additive] protected lemma IsLeftRegular.mul_eq_one_symm {a b : M} (reg : IsLeftRegular a)
    (eq : a * b = 1) : b * a = 1 :=
reg by simp [← mul_assoc, eq]

/--
lemma `IsRightRegular.mul_eq_one_symm` / 引理 `IsRightRegular.mul_eq_one_symm`

English:
lemma IsRightRegular.mul_eq_one_symm
  statement: {a b : M} (reg : IsRightRegular a)
  proof: reg by simp [mul_assoc, eq]

中文:
引理 IsRightRegular.mul_eq_one_symm
  结论: {a b : M} (reg : IsRightRegular a)
  证明: reg by simp [mul_assoc, eq]
-/
@[to_additive] protected lemma IsRightRegular.mul_eq_one_symm {a b : M} (reg : IsRightRegular a)
    (eq : b * a = 1) : a * b = 1 :=
reg by simp [mul_assoc, eq]

variable (M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLeftCancelMul
  signature: M] : IsDedekindFiniteMonoid M where
  body: (IsLeftCancelMul.mul_left_cancel _).mul_eq_one_symm

中文:
实例 [IsLeftCancelMul
  签名: M] : IsDedekindFiniteMonoid M where
  定义体: (IsLeftCancelMul.mul_left_cancel _).mul_eq_one_symm
-/
@[to_additive] instance [IsLeftCancelMul M] : IsDedekindFiniteMonoid M where
  mul_eq_one_symm := (IsLeftCancelMul.mul_left_cancel _).mul_eq_one_symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsRightCancelMul
  signature: M] : IsDedekindFiniteMonoid M where
  body: (IsRightCancelMul.mul_right_cancel _).mul_eq_one_symm

中文:
实例 [IsRightCancelMul
  签名: M] : IsDedekindFiniteMonoid M where
  定义体: (IsRightCancelMul.mul_right_cancel _).mul_eq_one_symm
-/
@[to_additive] instance [IsRightCancelMul M] : IsDedekindFiniteMonoid M where
  mul_eq_one_symm := (IsRightCancelMul.mul_right_cancel _).mul_eq_one_symm

namespace IsDedekindFiniteMonoid

/--
lemma `of_exists_self_mul_eq_one` / 引理 `of_exists_self_mul_eq_one`

English:
lemma of_exists_self_mul_eq_one
  given: (ex : forall x y : M, x * y = 1 -> exists z, y * z = 1)
  proof: by
    have ⟨z, hz⟩ := ex x y h
    rwa [show x = z by simpa [← mul_assoc, h] using congr_arg (x * ·) hz.symm]

中文:
引理 of_exists_self_mul_eq_one
  条件: (ex : 对任意 x y : M, x * y = 1 -> 存在 z, y * z = 1)
  证明: by
    have ⟨z, hz⟩ := ex x y h
    rwa [show x = z by simpa [← mul_assoc, h] using congr_arg (x * ·) hz.symm]
-/
@[to_additive] lemma of_exists_self_mul_eq_one (ex : forall x y : M, x * y = 1 -> exists z, y * z = 1) :
    IsDedekindFiniteMonoid M where
  mul_eq_one_symm {x y} h := by
    have ⟨z, hz⟩ := ex x y h
    rwa [show x = z by simpa [← mul_assoc, h] using congr_arg (x * ·) hz.symm]

/--
lemma `of_exists_mul_self_eq_one` / 引理 `of_exists_mul_self_eq_one`

English:
lemma of_exists_mul_self_eq_one
  given: (ex : forall x y : M, x * y = 1 -> exists z, z * x = 1)
  proof: by
    have ⟨z, hz⟩ := ex x y h
    rwa [show y = z by simpa [mul_assoc, h] using congr_arg (· * y) hz.symm]

中文:
引理 of_exists_mul_self_eq_one
  条件: (ex : 对任意 x y : M, x * y = 1 -> 存在 z, z * x = 1)
  证明: by
    have ⟨z, hz⟩ := ex x y h
    rwa [show y = z by simpa [mul_assoc, h] using congr_arg (· * y) hz.symm]
-/
@[to_additive] lemma of_exists_mul_self_eq_one (ex : forall x y : M, x * y = 1 -> exists z, z * x = 1) :
    IsDedekindFiniteMonoid M where
  mul_eq_one_symm {x y} h := by
    have ⟨z, hz⟩ := ex x y h
    rwa [show y = z by simpa [mul_assoc, h] using congr_arg (· * y) hz.symm]

end IsDedekindFiniteMonoid

end Monoid

/-- An additive monoid is torsion-free if scalar multiplication by every non-zero element `n : ℕ` is
injective. -/
@[mk_iff]
/--
Definition of `IsAddTorsionFree` / `IsAddTorsionFree` 的定义

English:
class IsAddTorsionFree
  parameters: (M : Type*) [AddMonoid M]
  axioms and operations (1):
    - nsmul_right_injective(⦃n) : Nat⦄ (hn : n != 0) : Injective fun a : M => n • a

中文:
类 IsAddTorsionFree
  参数: (M : 类型) [AddMonoid M]
  公理与运算 (1 个):
    - nsmul_right_injective(⦃n) : 自然数⦄ (hn : n != 0) : Injective fun a : M => n • a
-/
class IsAddTorsionFree (M : Type*) [AddMonoid M] where
  protected nsmul_right_injective ⦃n : Nat⦄ (hn : n != 0) : Injective fun a : M => n • a

/-- A monoid is torsion-free if power by every non-zero element `n : ℕ` is injective. -/
@[to_additive, mk_iff]
/--
Definition of `IsMulTorsionFree` / `IsMulTorsionFree` 的定义

English:
class IsMulTorsionFree
  parameters: (M : Type*) [Monoid M]
  axioms and operations (1):
    - pow_left_injective(⦃n) : Nat⦄ (hn : n != 0) : Injective fun a : M => a ^ n

中文:
类 IsMulTorsionFree
  参数: (M : 类型) [Monoid M]
  公理与运算 (1 个):
    - pow_left_injective(⦃n) : 自然数⦄ (hn : n != 0) : Injective fun a : M => a ^ n
-/
class IsMulTorsionFree (M : Type*) [Monoid M] where
  protected pow_left_injective ⦃n : Nat⦄ (hn : n != 0) : Injective fun a : M => a ^ n

attribute [to_additive existing] isMulTorsionFree_iff

/--
Definition of `AddCommMonoid` / `AddCommMonoid` 的定义

English:
class AddCommMonoid
  parameters: (M : Type u)
  extends: AddMonoid M, AddCommSemigroup M
  (no additional axioms)

中文:
类 AddCommMonoid
  参数: (M : 类型u)
  继承: AddMonoid M, AddCommSemigroup M
  (无附加公理)
-/
class AddCommMonoid (M : Type u) extends AddMonoid M, AddCommSemigroup M

/-- A commutative monoid is a monoid with commutative `(*)`. -/
@[to_additive]
/--
Definition of `CommMonoid` / `CommMonoid` 的定义

English:
class CommMonoid
  parameters: (M : Type u)
  extends: Monoid M, CommSemigroup M
  (no additional axioms)

中文:
类 CommMonoid
  参数: (M : 类型u)
  继承: Monoid M, CommSemigroup M
  (无附加公理)
-/
class CommMonoid (M : Type u) extends Monoid M, CommSemigroup M

/-- Shortcut instance for `IsCommutativeHMul M → IsDedekindFiniteMonoid M`.

This is assigned default rather than low priority because it gives the most common examples
of Dedekind-finite monoids and is used the most often. Benchmark results indicate default
priority performs better than low or high priority. -/
@[to_additive] instance (M) [CommMonoid M] : IsDedekindFiniteMonoid M := inferInstance

section LeftCancelMonoid

/--
Definition of `AddLeftCancelMonoid` / `AddLeftCancelMonoid` 的定义

English:
class AddLeftCancelMonoid
  parameters: (M : Type u)
  extends: AddMonoid M, AddLeftCancelSemigroup M
  (no additional axioms)

中文:
类 AddLeftCancelMonoid
  参数: (M : 类型u)
  继承: AddMonoid M, AddLeftCancelSemigroup M
  (无附加公理)
-/
class AddLeftCancelMonoid (M : Type u) extends AddMonoid M, AddLeftCancelSemigroup M

attribute [instance 75] AddLeftCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is left-cancellative. -/
@[to_additive]
/--
Definition of `LeftCancelMonoid` / `LeftCancelMonoid` 的定义

English:
class LeftCancelMonoid
  parameters: (M : Type u)
  extends: Monoid M, LeftCancelSemigroup M
  (no additional axioms)

中文:
类 LeftCancelMonoid
  参数: (M : 类型u)
  继承: Monoid M, LeftCancelSemigroup M
  (无附加公理)
-/
class LeftCancelMonoid (M : Type u) extends Monoid M, LeftCancelSemigroup M

attribute [instance 75] LeftCancelMonoid.toMonoid -- See note [lower cancel priority]

end LeftCancelMonoid

section RightCancelMonoid

/--
Definition of `AddRightCancelMonoid` / `AddRightCancelMonoid` 的定义

English:
class AddRightCancelMonoid
  parameters: (M : Type u)
  extends: AddMonoid M, AddRightCancelSemigroup M
  (no additional axioms)

中文:
类 AddRightCancelMonoid
  参数: (M : 类型u)
  继承: AddMonoid M, AddRightCancelSemigroup M
  (无附加公理)
-/
class AddRightCancelMonoid (M : Type u) extends AddMonoid M, AddRightCancelSemigroup M

attribute [instance 75] AddRightCancelMonoid.toAddMonoid -- See note [lower cancel priority]

/-- A monoid in which multiplication is right-cancellative. -/
@[to_additive]
/--
Definition of `RightCancelMonoid` / `RightCancelMonoid` 的定义

English:
class RightCancelMonoid
  parameters: (M : Type u)
  extends: Monoid M, RightCancelSemigroup M
  (no additional axioms)

中文:
类 RightCancelMonoid
  参数: (M : 类型u)
  继承: Monoid M, RightCancelSemigroup M
  (无附加公理)
-/
class RightCancelMonoid (M : Type u) extends Monoid M, RightCancelSemigroup M

attribute [instance 75] RightCancelMonoid.toMonoid -- See note [lower cancel priority]

end RightCancelMonoid

section CancelMonoid

/--
Definition of `AddCancelMonoid` / `AddCancelMonoid` 的定义

English:
class AddCancelMonoid
  parameters: (M : Type u)
  extends: AddLeftCancelMonoid M, AddRightCancelMonoid M
  (no additional axioms)

中文:
类 AddCancelMonoid
  参数: (M : 类型u)
  继承: AddLeftCancelMonoid M, AddRightCancelMonoid M
  (无附加公理)
-/
class AddCancelMonoid (M : Type u) extends AddLeftCancelMonoid M, AddRightCancelMonoid M

/-- A monoid in which multiplication is cancellative. -/
@[to_additive]
/--
Definition of `CancelMonoid` / `CancelMonoid` 的定义

English:
class CancelMonoid
  parameters: (M : Type u)
  extends: LeftCancelMonoid M, RightCancelMonoid M
  (no additional axioms)

中文:
类 CancelMonoid
  参数: (M : 类型u)
  继承: LeftCancelMonoid M, RightCancelMonoid M
  (无附加公理)
-/
class CancelMonoid (M : Type u) extends LeftCancelMonoid M, RightCancelMonoid M

/--
Definition of `AddCancelCommMonoid` / `AddCancelCommMonoid` 的定义

English:
class AddCancelCommMonoid
  parameters: (M : Type u)
  extends: AddCommMonoid M, AddLeftCancelMonoid M
  (no additional axioms)

中文:
类 AddCancelCommMonoid
  参数: (M : 类型u)
  继承: AddCommMonoid M, AddLeftCancelMonoid M
  (无附加公理)
-/
class AddCancelCommMonoid (M : Type u) extends AddCommMonoid M, AddLeftCancelMonoid M

attribute [instance 75] AddCancelCommMonoid.toAddCommMonoid -- See note [lower cancel priority]

/-- Commutative version of `CancelMonoid`. -/
@[to_additive]
/--
Definition of `CancelCommMonoid` / `CancelCommMonoid` 的定义

English:
class CancelCommMonoid
  parameters: (M : Type u)
  extends: CommMonoid M, LeftCancelMonoid M
  (no additional axioms)

中文:
类 CancelCommMonoid
  参数: (M : 类型u)
  继承: CommMonoid M, LeftCancelMonoid M
  (无附加公理)
-/
class CancelCommMonoid (M : Type u) extends CommMonoid M, LeftCancelMonoid M

attribute [instance 75] CancelCommMonoid.toCommMonoid -- See note [lower cancel priority]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CancelCommMonoid.toCancelMonoid (M : Type u) [CancelCommMonoid M] :
    CancelMonoid M :=
  { CommMagma.IsLeftCancelMul.toIsRightCancelMul M with }

/-- Any `CancelMonoid G` satisfies `IsCancelMul G`. -/
@[to_additive /-- Any `AddCancelMonoid G` satisfies `IsCancelAdd G`. -/]
instance (priority := 100) CancelMonoid.toIsCancelMul (M : Type u) [CancelMonoid M] :
    IsCancelMul M where

end CancelMonoid

/--
Definition of `zpowRec` / `zpowRec` 的定义

English:
definition zpowRec
  signature: [One G] [Mul G] [Inv G] (npow : Nat -> G -> G := npowRec)

中文:
定义 zpowRec
  签名: [One G] [Mul G] [Inv G] (npow : 自然数 -> G -> G := npowRec)

Depends on / 依赖: npowRec
-/
def zpowRec [One G] [Mul G] [Inv G] (npow : Nat -> G -> G := npowRec) : Int -> G -> G
  | Int.ofNat n, a => npow n a
  | Int.negSucc n, a => (npow n.succ a)⁻¹

/--
Definition of `zsmulRec` / `zsmulRec` 的定义

English:
definition zsmulRec
  signature: [Zero G] [Add G] [Neg G] (nsmul : Nat -> G -> G := nsmulRec)

中文:
定义 zsmulRec
  签名: [Zero G] [Add G] [Neg G] (nsmul : 自然数 -> G -> G := nsmulRec)

Depends on / 依赖: nsmulRec
-/
def zsmulRec [Zero G] [Add G] [Neg G] (nsmul : Nat -> G -> G := nsmulRec) : Int -> G -> G
  | Int.ofNat n, a => nsmul n a
  | Int.negSucc n, a => -nsmul n.succ a

attribute [to_additive existing] zpowRec

section InvolutiveInv

/--
Definition of `InvolutiveNeg` / `InvolutiveNeg` 的定义

English:
class InvolutiveNeg
  parameters: (A : Type*)
  extends: Neg A
  axioms and operations (1):
    - neg_neg : forall x : A, - -x = x

中文:
类 InvolutiveNeg
  参数: (A : 类型)
  继承: Neg A
  公理与运算 (1 个):
    - neg_neg : 对任意 x : A, - -x = x
-/
class InvolutiveNeg (A : Type*) extends Neg A where
  protected neg_neg : forall x : A, - -x = x

/-- Auxiliary typeclass for types with an involutive `Inv`. -/
@[to_additive]
/--
Definition of `InvolutiveInv` / `InvolutiveInv` 的定义

English:
class InvolutiveInv
  parameters: (G : Type*)
  extends: Inv G
  axioms and operations (1):
    - inv_inv : forall x : G, x⁻¹⁻¹ = x

中文:
类 InvolutiveInv
  参数: (G : 类型)
  继承: Inv G
  公理与运算 (1 个):
    - inv_inv : 对任意 x : G, x⁻¹⁻¹ = x
-/
class InvolutiveInv (G : Type*) extends Inv G where
  protected inv_inv : forall x : G, x⁻¹⁻¹ = x

variable [InvolutiveInv G]

@[to_additive (attr := simp)]
/--
theorem `inv_inv` / 定理 `inv_inv`

English:
theorem inv_inv
  given: (a : G)
  statement: a⁻¹⁻¹ = a
  proof: InvolutiveInv.inv_inv _

中文:
定理 inv_inv
  条件: (a : G)
  结论: a⁻¹⁻¹ = a
  证明: InvolutiveInv.inv_inv _

Depends on / 依赖: InvolutiveInv, InvolutiveInv.inv_inv, inv_inv
-/
theorem inv_inv (a : G) : a⁻¹⁻¹ = a :=
  InvolutiveInv.inv_inv _

end InvolutiveInv

/-!
### Design note on `DivInvMonoid`/`SubNegMonoid` and `DivisionMonoid`/`SubtractionMonoid`

Those two pairs of made-up classes fulfill slightly different roles.

`DivInvMonoid`/`SubNegMonoid` provides the minimum amount of information to define the
`ℤ` action (`zpow` or `zsmul`). Further, it provides a `div` field, matching the forgetful
inheritance pattern. This is useful to shorten extension clauses of stronger structures (`Group`,
`GroupWithZero`, `DivisionRing`, `Field`) and for a few structures with a rather weak
pseudo-inverse (`Matrix`).

`DivisionMonoid`/`SubtractionMonoid` is targeted at structures with stronger pseudo-inverses. It
is an ad hoc collection of axioms that are mainly respected by three things:
* Groups
* Groups with zero
* The pointwise monoids `Set α`, `Finset α`, `Filter α`

It acts as a middle ground for structures with an inversion operator that plays well with
multiplication, except for the fact that it might not be a true inverse (`a / a ≠ 1` in general).
The axioms are pretty arbitrary (many other combinations are equivalent to it), but they are
independent:
* Without `DivisionMonoid.div_eq_mul_inv`, you can define `/` arbitrarily.
* Without `DivisionMonoid.inv_inv`, you can consider `WithTop Unit` with `a⁻¹ = ⊤` for all `a`.
* Without `DivisionMonoid.mul_inv_rev`, you can consider `WithTop α` with `a⁻¹ = a` for all `a`
  where `α` noncommutative.
* Without `DivisionMonoid.inv_eq_of_mul`, you can consider any `CommMonoid` with `a⁻¹ = a` for all
  `a`.

As a consequence, a few natural structures do not fit in this framework. For example, `ENNReal`
respects everything except for the fact that `(0 * ∞)⁻¹ = 0⁻¹ = ∞` while `∞⁻¹ * 0⁻¹ = 0 * ∞ = 0`.
-/

/--
Definition of `DivInvMonoid.div'` / `DivInvMonoid.div'` 的定义

English:
definition DivInvMonoid.div'
  signature: {G : Type u} [Monoid G] [Inv G] (a b : G)
  body: a * b⁻¹

中文:
定义 DivInvMonoid.div'
  签名: {G : 类型u} [Monoid G] [Inv G] (a b : G)
  定义体: a * b⁻¹
-/
def DivInvMonoid.div' {G : Type u} [Monoid G] [Inv G] (a b : G) : G := a * b⁻¹

/--
Definition of `ZSMul` / `ZSMul` 的定义

English:
class ZSMul
  parameters: (G : Type u)
  axioms and operations (1):
    - zsmul : Int -> G -> G

中文:
类 ZSMul
  参数: (G : 类型u)
  公理与运算 (1 个):
    - zsmul : 整数 -> G -> G
-/
class ZSMul (G : Type u) where
  /-- Multiplication by an integer.
  Set this to `zsmulRec` unless `Module` diamonds are possible. -/
  protected zsmul : Int -> G -> G

/-- `ZPow` is an implementation detail of `DivInvMonoid`. It is needed because it is
impossible to extend `Pow M ℕ` and `Pow M ℤ` at the same time. -/
@[to_additive]
/--
Definition of `ZPow` / `ZPow` 的定义

English:
class ZPow
  parameters: (G : Type u)
  axioms and operations (1):
    - zpow : Int -> G -> G

中文:
类 ZPow
  参数: (G : 类型u)
  公理与运算 (1 个):
    - zpow : 整数 -> G -> G
-/
class ZPow (G : Type u) where
  /-- The power operation: `a ^ n = a * ··· * a`; `a ^ (-n) = a⁻¹ * ··· a⁻¹` (`n` times) -/
  protected zpow : Int -> G -> G

@[to_additive toSMul]
/--
Instance `ZPow.toPow` / 实例 `ZPow.toPow`

English:
instance ZPow.toPow
  signature: {M : Type*} [ZPow M]
  body: ⟨fun x n => ZPow.zpow n x⟩

@[to_additive ofSMul]

中文:
实例 ZPow.toPow
  签名: {M : 类型} [ZPow M]
  定义体: ⟨fun x n => ZPow.zpow n x⟩

@[to_additive ofSMul]

Depends on / 依赖: ZPow.zpow
-/
instance ZPow.toPow {M : Type*} [ZPow M] : Pow M Int :=
  ⟨fun x n => ZPow.zpow n x⟩

@[to_additive ofSMul]
/--
Instance `ZPow.ofPow` / 实例 `ZPow.ofPow`

English:
instance ZPow.ofPow
  signature: {M : Type*} [Pow M Int]
  body: ⟨fun n x => Pow.pow x n⟩

中文:
实例 ZPow.ofPow
  签名: {M : 类型} [Pow M 整数]
  定义体: ⟨fun n x => Pow.pow x n⟩

Depends on / 依赖: Pow.pow
-/
instance ZPow.ofPow {M : Type*} [Pow M Int] : ZPow M := ⟨fun n x => Pow.pow x n⟩

/--
Definition of `DivInvMonoid` / `DivInvMonoid` 的定义

English:
class DivInvMonoid
  parameters: (G : Type u)
  extends: Monoid G, Inv G, Div G, ZPow G
  axioms and operations (6):
    - div : = DivInvMonoid.div'
    - div_eq_mul_inv : forall a b : G, a / b = a * b⁻¹  [default: by intros; rfl]
    - zpow : = zpowRec npowRec
    - zpow_zero'((a : G)) : a ^ (0 : Int) = 1  [default: by intros; rfl]
    - zpow_succ'((n : Nat) (a : G)) : a ^ (n.succ : Int) = a ^ (n : Int) * a  [default: by intros; rfl]
    - zpow_neg'((n : Nat) (a : G)) : a ^ Int.negSucc n = (a ^ (n.succ : Int))⁻¹  [default: by intros; rfl]

中文:
类 DivInvMonoid
  参数: (G : 类型u)
  继承: Monoid G, Inv G, Div G, ZPow G
  公理与运算 (6 个):
    - div : = DivInvMonoid.div'
    - div_eq_mul_inv : 对任意 a b : G, a / b = a * b⁻¹  [默认: by intros; rfl]
    - zpow : = zpowRec npowRec
    - zpow_zero'((a : G)) : a ^ (0 : 整数) = 1  [默认: by intros; rfl]
    - zpow_succ'((n : 自然数) (a : G)) : a ^ (n.succ : 整数) = a ^ (n : 整数) * a  [默认: by intros; rfl]
    - zpow_neg'((n : 自然数) (a : G)) : a ^ 整数.negSucc n = (a ^ (n.succ : 整数))⁻¹  [默认: by intros; rfl]

Depends on / 依赖: DivInvMonoid, DivInvMonoid.div
-/
class DivInvMonoid (G : Type u) extends Monoid G, Inv G, Div G, ZPow G where
  protected div := DivInvMonoid.div'
  /-- `a / b := a * b⁻¹` -/
  protected div_eq_mul_inv : forall a b : G, a / b = a * b⁻¹ := by intros; rfl
  zpow := zpowRec npowRec
  /-- `a ^ 0 = 1` -/
  protected zpow_zero' (a : G) : a ^ (0 : Int) = 1 := by intros; rfl
  /-- `a ^ (n + 1) = a ^ n * a` -/
  protected zpow_succ' (n : Nat) (a : G) : a ^ (n.succ : Int) = a ^ (n : Int) * a := by
    intros; rfl
  /-- `a ^ -(n + 1) = (a ^ (n + 1))⁻¹` -/
  protected zpow_neg' (n : Nat) (a : G) : a ^ Int.negSucc n = (a ^ (n.succ : Int))⁻¹ := by intros; rfl

/--
Definition of `SubNegMonoid.sub'` / `SubNegMonoid.sub'` 的定义

English:
definition SubNegMonoid.sub'
  signature: {G : Type u} [AddMonoid G] [Neg G] (a b : G)
  body: a + -b

中文:
定义 SubNegMonoid.sub'
  签名: {G : 类型u} [AddMonoid G] [Neg G] (a b : G)
  定义体: a + -b
-/
def SubNegMonoid.sub' {G : Type u} [AddMonoid G] [Neg G] (a b : G) : G := a + -b

attribute [to_additive existing SubNegMonoid.sub'] DivInvMonoid.div'

/--
Definition of `SubNegMonoid` / `SubNegMonoid` 的定义

English:
class SubNegMonoid
  parameters: (G : Type u)
  extends: AddMonoid G, Neg G, Sub G, ZSMul G
  axioms and operations (5):
    - sub : = SubNegMonoid.sub'
    - sub_eq_add_neg : forall a b : G, a - b = a + -b  [default: by intros; rfl]
    - zsmul_zero'((a : G)) : (0 : Int) • a = 0  [default: by intros; rfl]
    - zsmul_succ'((n : Nat) (a : G)) : (n.succ : Int) • a = (n : Int) • a + a  [default: by intros; rfl]
    - zsmul_neg'((n : Nat) (a : G)) : (Int.negSucc n) • a = -((n.succ : Int) • a)  [default: by intros; rfl]

中文:
类 SubNegMonoid
  参数: (G : 类型u)
  继承: AddMonoid G, Neg G, Sub G, ZSMul G
  公理与运算 (5 个):
    - sub : = SubNegMonoid.sub'
    - sub_eq_add_neg : 对任意 a b : G, a - b = a + -b  [默认: by intros; rfl]
    - zsmul_zero'((a : G)) : (0 : 整数) • a = 0  [默认: by intros; rfl]
    - zsmul_succ'((n : 自然数) (a : G)) : (n.succ : 整数) • a = (n : 整数) • a + a  [默认: by intros; rfl]
    - zsmul_neg'((n : 自然数) (a : G)) : (整数.negSucc n) • a = -((n.succ : 整数) • a)  [默认: by intros; rfl]

Depends on / 依赖: SubNegMonoid, SubNegMonoid.sub
-/
class SubNegMonoid (G : Type u) extends AddMonoid G, Neg G, Sub G, ZSMul G where
  protected sub := SubNegMonoid.sub'
  protected sub_eq_add_neg : forall a b : G, a - b = a + -b := by intros; rfl
  protected zsmul_zero' (a : G) : (0 : Int) • a = 0 := by intros; rfl
  protected zsmul_succ' (n : Nat) (a : G) :
      (n.succ : Int) • a = (n : Int) • a + a := by
    intros; rfl
  protected zsmul_neg' (n : Nat) (a : G) : (Int.negSucc n) • a = -((n.succ : Int) • a) := by
    intros; rfl

attribute [to_additive SubNegMonoid] DivInvMonoid

/--
Definition of `IsAddCyclic` / `IsAddCyclic` 的定义

English:
class IsAddCyclic
  parameters: (G : Type u) [SMul Int G]
  axioms and operations (1):
    - exists_zsmul_surjective : exists g : G, Function.Surjective (· • g : Int -> G)

中文:
类 IsAddCyclic
  参数: (G : 类型u) [SMul 整数 G]
  公理与运算 (1 个):
    - exists_zsmul_surjective : 存在 g : G, Function.Surjective (· • g : 整数 -> G)
-/
class IsAddCyclic (G : Type u) [SMul Int G] : Prop where
  protected exists_zsmul_surjective : exists g : G, Function.Surjective (· • g : Int -> G)

/-- A group is called *cyclic* if it is generated by a single element. -/
@[to_additive (attr := wikidata Q245462)]
/--
Definition of `IsCyclic` / `IsCyclic` 的定义

English:
class IsCyclic
  parameters: (G : Type u) [Pow G Int]
  axioms and operations (1):
    - exists_zpow_surjective : exists g : G, Function.Surjective (g ^ · : Int -> G)

中文:
类 IsCyclic
  参数: (G : 类型u) [Pow G 整数]
  公理与运算 (1 个):
    - exists_zpow_surjective : 存在 g : G, Function.Surjective (g ^ · : 整数 -> G)
-/
class IsCyclic (G : Type u) [Pow G Int] : Prop where
  protected exists_zpow_surjective : exists g : G, Function.Surjective (g ^ · : Int -> G)

@[to_additive]
/--
theorem `exists_zpow_surjective` / 定理 `exists_zpow_surjective`

English:
theorem exists_zpow_surjective
  given: (G : Type*) [Pow G Int] [IsCyclic G]
  proof: IsCyclic.exists_zpow_surjective

中文:
定理 exists_zpow_surjective
  条件: (G : 类型) [Pow G 整数] [IsCyclic G]
  证明: IsCyclic.exists_zpow_surjective

Depends on / 依赖: IsCyclic, IsCyclic.exists_zpow_surjective, exists_zpow_surjective
-/
theorem exists_zpow_surjective (G : Type*) [Pow G Int] [IsCyclic G] :
    exists g : G, Function.Surjective (g ^ · : Int -> G) :=
  IsCyclic.exists_zpow_surjective

section DivInvMonoid

variable [DivInvMonoid G]

/--
theorem `zpow_eq_pow` / 定理 `zpow_eq_pow`

English:
theorem zpow_eq_pow
  given: (n : Int) (x : G)
  proof: rfl

中文:
定理 zpow_eq_pow
  条件: (n : 整数) (x : G)
  证明: rfl
-/
@[to_additive (attr := simp) zsmul_eq_smul] theorem zpow_eq_pow (n : Int) (x : G) :
    ZPow.zpow n x = x ^ n :=
  rfl

/--
theorem `zpow_zero` / 定理 `zpow_zero`

English:
theorem zpow_zero
  given: (a : G)
  statement: a ^ (0 : Int) = 1
  proof: DivInvMonoid.zpow_zero' a

中文:
定理 zpow_zero
  条件: (a : G)
  结论: a ^ (0 : 整数) = 1
  证明: DivInvMonoid.zpow_zero' a
-/
@[to_additive zero_zsmul] theorem zpow_zero (a : G) : a ^ (0 : Int) = 1 :=
  DivInvMonoid.zpow_zero' a

-- `zpow_zero` is provable by `simp` (via `zpow_ofNat`), so the `simpNF` linter rejects tagging it.
-- We still want the additive `zero_zsmul` to be `simp`, so we tag that one manually.
attribute [simp] zero_zsmul

@[to_additive (attr := simp, norm_cast) natCast_zsmul]
/--
theorem `zpow_natCast` / 定理 `zpow_natCast`

English:
theorem zpow_natCast
  given: (a : G)
  statement: forall n : Nat, a ^ (n : Int) = a ^ n
  proof: DivInvMonoid.zpow_succ' _ _
    _ = a ^ n * a := congrArg (· * a) (zpow_natCast a n)
    _ = a ^ (n + 1) := (pow_succ _ _).symm

中文:
定理 zpow_natCast
  条件: (a : G)
  结论: 对任意 n : 自然数, a ^ (n : 整数) = a ^ n
  证明: DivInvMonoid.zpow_succ' _ _
    _ = a ^ n * a := congrArg (· * a) (zpow_natCast a n)
    _ = a ^ (n + 1) := (pow_succ _ _).symm

Depends on / 依赖: DivInvMonoid, DivInvMonoid.zpow_succ, zpow_succ
-/
theorem zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^ n
  | 0 => (zpow_zero _).trans (pow_zero _).symm
  | n + 1 => calc
    a ^ (↑(n + 1) : Int) = a ^ (n : Int) * a := DivInvMonoid.zpow_succ' _ _
    _ = a ^ n * a := congrArg (· * a) (zpow_natCast a n)
    _ = a ^ (n + 1) := (pow_succ _ _).symm


-- TODO: consider also making `ofNat_zsmul` a `simp` lemma; it is currently not, because it breaks
-- `simp`-normal forms involving `(2 : ℤ) • ·` used in the theory of oriented angles.
@[to_additive ofNat_zsmul, simp]
/--
lemma `zpow_ofNat` / 引理 `zpow_ofNat`

English:
lemma zpow_ofNat
  given: (a : G) (n : Nat)
  statement: a ^ (ofNat(n) : Int) = a ^ OfNat.ofNat n
  proof: zpow_natCast ..

中文:
引理 zpow_ofNat
  条件: (a : G) (n : 自然数)
  结论: a ^ (of自然数(n) : 整数) = a ^ Of自然数.of自然数 n
  证明: zpow_natCast ..

Depends on / 依赖: zpow_natCast
-/
lemma zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ OfNat.ofNat n :=
  zpow_natCast ..

/--
theorem `zpow_negSucc` / 定理 `zpow_negSucc`

English:
theorem zpow_negSucc
  given: (a : G) (n : Nat)
  statement: a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹
  proof: by
  rw [← zpow_natCast]
  exact DivInvMonoid.zpow_neg' n a

中文:
定理 zpow_negSucc
  条件: (a : G) (n : 自然数)
  结论: a ^ (整数.negSucc n) = (a ^ (n + 1))⁻¹
  证明: by
  rw [← zpow_natCast]
  exact DivInvMonoid.zpow_neg' n a

Depends on / 依赖: DivInvMonoid, DivInvMonoid.zpow_neg, zpow_natCast, zpow_neg
-/
theorem zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a ^ (n + 1))⁻¹ := by
  rw [← zpow_natCast]
  exact DivInvMonoid.zpow_neg' n a

/--
theorem `negSucc_zsmul` / 定理 `negSucc_zsmul`

English:
theorem negSucc_zsmul
  given: {G} [SubNegMonoid G] (a : G) (n : Nat)
  proof: by
  rw [← natCast_zsmul]
  exact SubNegMonoid.zsmul_neg' n a

中文:
定理 negSucc_zsmul
  条件: {G} [SubNegMonoid G] (a : G) (n : 自然数)
  证明: by
  rw [← natCast_zsmul]
  exact SubNegMonoid.zsmul_neg' n a

Depends on / 依赖: SubNegMonoid, SubNegMonoid.zsmul_neg, natCast_zsmul, zsmul_neg
-/
theorem negSucc_zsmul {G} [SubNegMonoid G] (a : G) (n : Nat) :
    Int.negSucc n • a = -((n + 1) • a) := by
  rw [← natCast_zsmul]
  exact SubNegMonoid.zsmul_neg' n a

attribute [to_additive existing (attr := simp) negSucc_zsmul] zpow_negSucc

/-- Dividing by an element is the same as multiplying by its inverse.

This is a duplicate of `DivInvMonoid.div_eq_mul_inv` ensuring that the types unfold better.
-/
@[to_additive /-- Subtracting an element is the same as adding by its negative.
This is a duplicate of `SubNegMonoid.sub_eq_add_neg` ensuring that the types unfold better. -/]
/--
theorem `div_eq_mul_inv` / 定理 `div_eq_mul_inv`

English:
theorem div_eq_mul_inv
  given: (a b : G)
  statement: a / b = a * b⁻¹
  proof: DivInvMonoid.div_eq_mul_inv _ _

alias division_def := div_eq_mul_inv

@[to_additive]

中文:
定理 div_eq_mul_inv
  条件: (a b : G)
  结论: a / b = a * b⁻¹
  证明: DivInvMonoid.div_eq_mul_inv _ _

alias division_def := div_eq_mul_inv

@[to_additive]

Depends on / 依赖: DivInvMonoid, DivInvMonoid.div_eq_mul_inv, div_eq_mul_inv
-/
theorem div_eq_mul_inv (a b : G) : a / b = a * b⁻¹ :=
  DivInvMonoid.div_eq_mul_inv _ _

alias division_def := div_eq_mul_inv

@[to_additive]
/--
theorem `inv_eq_one_div` / 定理 `inv_eq_one_div`

English:
theorem inv_eq_one_div
  given: (x : G)
  statement: x⁻¹ = 1 / x
  proof: by rw [div_eq_mul_inv, one_mul]

@[to_additive]

中文:
定理 inv_eq_one_div
  条件: (x : G)
  结论: x⁻¹ = 1 / x
  证明: by rw [div_eq_mul_inv, one_mul]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, one_mul
-/
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]

@[to_additive]
/--
theorem `mul_div_assoc` / 定理 `mul_div_assoc`

English:
theorem mul_div_assoc
  given: (a b c : G)
  statement: a * b / c = a * (b / c)
  proof: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_assoc]

@[to_additive (attr := simp)]

中文:
定理 mul_div_assoc
  条件: (a b c : G)
  结论: a * b / c = a * (b / c)
  证明: by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_assoc]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, mul_assoc
-/
theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by
  rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_assoc]

@[to_additive (attr := simp)]
/--
theorem `one_div` / 定理 `one_div`

English:
theorem one_div
  given: (a : G)
  statement: 1 / a = a⁻¹
  proof: (inv_eq_one_div a).symm

@[to_additive one_zsmul]

中文:
定理 one_div
  条件: (a : G)
  结论: 1 / a = a⁻¹
  证明: (inv_eq_one_div a).symm

@[to_additive one_zsmul]

Depends on / 依赖: inv_eq_one_div
-/
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm

@[to_additive one_zsmul]
/--
lemma `zpow_one` / 引理 `zpow_one`

English:
lemma zpow_one
  given: (a : G)
  statement: a ^ (1 : Int) = a
  proof: by rw [zpow_ofNat, pow_one]

中文:
引理 zpow_one
  条件: (a : G)
  结论: a ^ (1 : 整数) = a
  证明: by rw [zpow_ofNat, pow_one]

Depends on / 依赖: pow_one, zpow_ofNat
-/
lemma zpow_one (a : G) : a ^ (1 : Int) = a := by rw [zpow_ofNat, pow_one]

-- `zpow_one` is provable by `simp` (via `zpow_ofNat`), so the `simpNF` linter rejects tagging it.
-- We still want the additive `one_zsmul` to be `simp`, so we tag that one manually.
attribute [simp] one_zsmul

/--
lemma `zpow_two` / 引理 `zpow_two`

English:
lemma zpow_two
  given: (a : G)
  statement: a ^ (2 : Int) = a * a
  proof: by rw [zpow_ofNat, pow_two]

@[to_additive neg_one_zsmul]

中文:
引理 zpow_two
  条件: (a : G)
  结论: a ^ (2 : 整数) = a * a
  证明: by rw [zpow_ofNat, pow_two]

@[to_additive neg_one_zsmul]
-/
@[to_additive two_zsmul] lemma zpow_two (a : G) : a ^ (2 : Int) = a * a := by rw [zpow_ofNat, pow_two]

@[to_additive neg_one_zsmul]
/--
lemma `zpow_neg_one` / 引理 `zpow_neg_one`

English:
lemma zpow_neg_one
  given: (x : G)
  statement: x ^ (-1 : Int) = x⁻¹
  proof: (zpow_negSucc x 0).trans congr_arg Inv.inv (pow_one x)

@[to_additive]

中文:
引理 zpow_neg_one
  条件: (x : G)
  结论: x ^ (-1 : 整数) = x⁻¹
  证明: (zpow_negSucc x 0).trans congr_arg Inv.inv (pow_one x)

@[to_additive]

Depends on / 依赖: Inv.inv, congr_arg, pow_one, zpow_negSucc
-/
lemma zpow_neg_one (x : G) : x ^ (-1 : Int) = x⁻¹ :=
(zpow_negSucc x 0).trans congr_arg Inv.inv (pow_one x)

@[to_additive]
/--
lemma `zpow_neg_coe_of_pos` / 引理 `zpow_neg_coe_of_pos`

English:
lemma zpow_neg_coe_of_pos
  given: (a : G)
  statement: forall {n : Nat}, 0 < n -> a ^ (-(n : Int)) = (a ^ n)⁻¹

中文:
引理 zpow_neg_coe_of_pos
  条件: (a : G)
  结论: 对任意 {n : 自然数}, 0 < n -> a ^ (-(n : 整数)) = (a ^ n)⁻¹
-/
lemma zpow_neg_coe_of_pos (a : G) : forall {n : Nat}, 0 < n -> a ^ (-(n : Int)) = (a ^ n)⁻¹
  | _ + 1, _ => zpow_negSucc _ _

end DivInvMonoid

section InvOneClass

/--
Definition of `NegZeroClass` / `NegZeroClass` 的定义

English:
class NegZeroClass
  parameters: (G : Type*)
  extends: Zero G, Neg G
  axioms and operations (1):
    - neg_zero : -(0 : G) = 0

中文:
类 NegZeroClass
  参数: (G : 类型)
  继承: Zero G, Neg G
  公理与运算 (1 个):
    - neg_zero : -(0 : G) = 0
-/
class NegZeroClass (G : Type*) extends Zero G, Neg G where
  protected neg_zero : -(0 : G) = 0

/--
Definition of `SubNegZeroMonoid` / `SubNegZeroMonoid` 的定义

English:
class SubNegZeroMonoid
  parameters: (G : Type*)
  extends: SubNegMonoid G, NegZeroClass G
  (no additional axioms)

中文:
类 SubNegZeroMonoid
  参数: (G : 类型)
  继承: SubNegMonoid G, NegZeroClass G
  (无附加公理)
-/
class SubNegZeroMonoid (G : Type*) extends SubNegMonoid G, NegZeroClass G

/-- Typeclass for expressing that `1⁻¹ = 1`. -/
@[to_additive]
/--
Definition of `InvOneClass` / `InvOneClass` 的定义

English:
class InvOneClass
  parameters: (G : Type*)
  extends: One G, Inv G
  axioms and operations (1):
    - inv_one : (1 : G)⁻¹ = 1

中文:
类 InvOneClass
  参数: (G : 类型)
  继承: One G, Inv G
  公理与运算 (1 个):
    - inv_one : (1 : G)⁻¹ = 1
-/
class InvOneClass (G : Type*) extends One G, Inv G where
  protected inv_one : (1 : G)⁻¹ = 1

/-- A `DivInvMonoid` where `1⁻¹ = 1`. -/
@[to_additive]
/--
Definition of `DivInvOneMonoid` / `DivInvOneMonoid` 的定义

English:
class DivInvOneMonoid
  parameters: (G : Type*)
  extends: DivInvMonoid G, InvOneClass G
  (no additional axioms)

中文:
类 DivInvOneMonoid
  参数: (G : 类型)
  继承: DivInvMonoid G, InvOneClass G
  (无附加公理)
-/
class DivInvOneMonoid (G : Type*) extends DivInvMonoid G, InvOneClass G

variable [InvOneClass G]

@[to_additive (attr := simp)]
/--
theorem `inv_one` / 定理 `inv_one`

English:
theorem inv_one
  statement: (1 : G)⁻¹ = 1
  proof: InvOneClass.inv_one

中文:
定理 inv_one
  结论: (1 : G)⁻¹ = 1
  证明: InvOneClass.inv_one

Depends on / 依赖: InvOneClass, InvOneClass.inv_one, inv_one
-/
theorem inv_one : (1 : G)⁻¹ = 1 :=
  InvOneClass.inv_one

end InvOneClass

/--
Definition of `SubtractionMonoid` / `SubtractionMonoid` 的定义

English:
class SubtractionMonoid
  parameters: (G : Type u)
  extends: SubNegMonoid G, InvolutiveNeg G
  axioms and operations (2):
    - neg_add_rev((a b : G)) : -(a + b) = -b + -a
    - neg_eq_of_add((a b : G)) : a + b = 0 -> -a = b

中文:
类 SubtractionMonoid
  参数: (G : 类型u)
  继承: SubNegMonoid G, InvolutiveNeg G
  公理与运算 (2 个):
    - neg_add_rev((a b : G)) : -(a + b) = -b + -a
    - neg_eq_of_add((a b : G)) : a + b = 0 -> -a = b
-/
class SubtractionMonoid (G : Type u) extends SubNegMonoid G, InvolutiveNeg G where
  protected neg_add_rev (a b : G) : -(a + b) = -b + -a
  /-- Despite the asymmetry of `neg_eq_of_add`, the symmetric version is true thanks to the
  involutivity of negation. -/
  protected neg_eq_of_add (a b : G) : a + b = 0 -> -a = b

/-- A `DivisionMonoid` is a `DivInvMonoid` with involutive inversion and such that
`(a * b)⁻¹ = b⁻¹ * a⁻¹` and `a * b = 1 → a⁻¹ = b`.

This is the immediate common ancestor of `Group` and `GroupWithZero`. -/
@[to_additive]
/--
Definition of `DivisionMonoid` / `DivisionMonoid` 的定义

English:
class DivisionMonoid
  parameters: (G : Type u)
  extends: DivInvMonoid G, InvolutiveInv G
  axioms and operations (2):
    - mul_inv_rev((a b : G)) : (a * b)⁻¹ = b⁻¹ * a⁻¹
    - inv_eq_of_mul((a b : G)) : a * b = 1 -> a⁻¹ = b

中文:
类 DivisionMonoid
  参数: (G : 类型u)
  继承: DivInvMonoid G, InvolutiveInv G
  公理与运算 (2 个):
    - mul_inv_rev((a b : G)) : (a * b)⁻¹ = b⁻¹ * a⁻¹
    - inv_eq_of_mul((a b : G)) : a * b = 1 -> a⁻¹ = b
-/
class DivisionMonoid (G : Type u) extends DivInvMonoid G, InvolutiveInv G where
  protected mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
  /-- Despite the asymmetry of `inv_eq_of_mul`, the symmetric version is true thanks to the
  involutivity of inversion. -/
  protected inv_eq_of_mul (a b : G) : a * b = 1 -> a⁻¹ = b

section DivisionMonoid

variable [DivisionMonoid G] {a b : G}

@[to_additive (attr := simp) neg_add_rev]
/--
theorem `mul_inv_rev` / 定理 `mul_inv_rev`

English:
theorem mul_inv_rev
  given: (a b : G)
  statement: (a * b)⁻¹ = b⁻¹ * a⁻¹
  proof: DivisionMonoid.mul_inv_rev _ _

@[to_additive]

中文:
定理 mul_inv_rev
  条件: (a b : G)
  结论: (a * b)⁻¹ = b⁻¹ * a⁻¹
  证明: DivisionMonoid.mul_inv_rev _ _

@[to_additive]

Depends on / 依赖: DivisionMonoid, DivisionMonoid.mul_inv_rev, mul_inv_rev
-/
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  DivisionMonoid.mul_inv_rev _ _

@[to_additive]
/--
theorem `inv_eq_of_mul_eq_one_right` / 定理 `inv_eq_of_mul_eq_one_right`

English:
theorem inv_eq_of_mul_eq_one_right
  statement: a * b = 1 -> a⁻¹ = b
  proof: DivisionMonoid.inv_eq_of_mul _ _

@[to_additive]

中文:
定理 inv_eq_of_mul_eq_one_right
  结论: a * b = 1 -> a⁻¹ = b
  证明: DivisionMonoid.inv_eq_of_mul _ _

@[to_additive]

Depends on / 依赖: DivisionMonoid, DivisionMonoid.inv_eq_of_mul, inv_eq_of_mul
-/
theorem inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻¹ = b :=
  DivisionMonoid.inv_eq_of_mul _ _

@[to_additive]
/--
theorem `inv_eq_of_mul_eq_one_left` / 定理 `inv_eq_of_mul_eq_one_left`

English:
theorem inv_eq_of_mul_eq_one_left
  given: (h : a * b = 1)
  statement: b⁻¹ = a
  proof: by
  rw [← inv_eq_of_mul_eq_one_right h]; rw [inv_inv]

@[to_additive]

中文:
定理 inv_eq_of_mul_eq_one_left
  条件: (h : a * b = 1)
  结论: b⁻¹ = a
  证明: by
  rw [← inv_eq_of_mul_eq_one_right h]; rw [inv_inv]

@[to_additive]

Depends on / 依赖: inv_eq_of_mul_eq_one_right, inv_inv
-/
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by
  rw [← inv_eq_of_mul_eq_one_right h]; rw [inv_inv]

@[to_additive]
/--
theorem `eq_inv_of_mul_eq_one_left` / 定理 `eq_inv_of_mul_eq_one_left`

English:
theorem eq_inv_of_mul_eq_one_left
  given: (h : a * b = 1)
  statement: a = b⁻¹
  proof: (inv_eq_of_mul_eq_one_left h).symm

中文:
定理 eq_inv_of_mul_eq_one_left
  条件: (h : a * b = 1)
  结论: a = b⁻¹
  证明: (inv_eq_of_mul_eq_one_left h).symm

Depends on / 依赖: inv_eq_of_mul_eq_one_left
-/
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm

end DivisionMonoid

/--
Definition of `SubtractionCommMonoid` / `SubtractionCommMonoid` 的定义

English:
class SubtractionCommMonoid
  parameters: (G : Type u)
  extends: SubtractionMonoid G, AddCommMonoid G
  (no additional axioms)

中文:
类 SubtractionCommMonoid
  参数: (G : 类型u)
  继承: SubtractionMonoid G, AddCommMonoid G
  (无附加公理)
-/
class SubtractionCommMonoid (G : Type u) extends SubtractionMonoid G, AddCommMonoid G

/-- Commutative `DivisionMonoid`.

This is the immediate common ancestor of `CommGroup` and `CommGroupWithZero`. -/
@[to_additive SubtractionCommMonoid]
/--
Definition of `DivisionCommMonoid` / `DivisionCommMonoid` 的定义

English:
class DivisionCommMonoid
  parameters: (G : Type u)
  extends: DivisionMonoid G, CommMonoid G
  (no additional axioms)

中文:
类 DivisionCommMonoid
  参数: (G : 类型u)
  继承: DivisionMonoid G, CommMonoid G
  (无附加公理)
-/
class DivisionCommMonoid (G : Type u) extends DivisionMonoid G, CommMonoid G

/--
Definition of `Group` / `Group` 的定义

English:
class Group
  parameters: (G : Type u)
  extends: DivInvMonoid G
  axioms and operations (1):
    - inv_mul_cancel : forall a : G, a⁻¹ * a = 1

中文:
类 Group
  参数: (G : 类型u)
  继承: DivInvMonoid G
  公理与运算 (1 个):
    - inv_mul_cancel : 对任意 a : G, a⁻¹ * a = 1
-/
class Group (G : Type u) extends DivInvMonoid G where
  protected inv_mul_cancel : forall a : G, a⁻¹ * a = 1

/--
Definition of `AddGroup` / `AddGroup` 的定义

English:
class AddGroup
  parameters: (A : Type u)
  extends: SubNegMonoid A
  axioms and operations (1):
    - neg_add_cancel : forall a : A, -a + a = 0

中文:
类 AddGroup
  参数: (A : 类型u)
  继承: SubNegMonoid A
  公理与运算 (1 个):
    - neg_add_cancel : 对任意 a : A, -a + a = 0

Depends on / 依赖: Q83478, wikidata
-/
class AddGroup (A : Type u) extends SubNegMonoid A where
  protected neg_add_cancel : forall a : A, -a + a = 0

attribute [to_additive (attr := wikidata Q83478)] Group

section Group

variable [Group G] {a b : G}

@[to_additive (attr := simp)]
/--
theorem `inv_mul_cancel` / 定理 `inv_mul_cancel`

English:
theorem inv_mul_cancel
  given: (a : G)
  statement: a⁻¹ * a = 1
  proof: Group.inv_mul_cancel a

@[to_additive]

中文:
定理 inv_mul_cancel
  条件: (a : G)
  结论: a⁻¹ * a = 1
  证明: Group.inv_mul_cancel a

@[to_additive]

Depends on / 依赖: Group.inv_mul_cancel, inv_mul_cancel
-/
theorem inv_mul_cancel (a : G) : a⁻¹ * a = 1 :=
  Group.inv_mul_cancel a

@[to_additive]
/--
theorem `inv_eq_of_mul` / 定理 `inv_eq_of_mul`

English:
theorem inv_eq_of_mul
  given: (h : a * b = 1)
  statement: a⁻¹ = b
  proof: left_inv_eq_right_inv (inv_mul_cancel a) h

@[to_additive (attr := simp)]

中文:
定理 inv_eq_of_mul
  条件: (h : a * b = 1)
  结论: a⁻¹ = b
  证明: left_inv_eq_right_inv (inv_mul_cancel a) h

@[to_additive (attr := simp)]
-/
private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b :=
  left_inv_eq_right_inv (inv_mul_cancel a) h

@[to_additive (attr := simp)]
/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: (a : G)
  statement: a * a⁻¹ = 1
  proof: by
  rw [← inv_mul_cancel a⁻¹]; rw [inv_eq_of_mul (inv_mul_cancel a)]

@[to_additive (attr := simp) sub_self]

中文:
定理 mul_inv_cancel
  条件: (a : G)
  结论: a * a⁻¹ = 1
  证明: by
  rw [← inv_mul_cancel a⁻¹]; rw [inv_eq_of_mul (inv_mul_cancel a)]

@[to_additive (attr := simp) sub_self]

Depends on / 依赖: inv_eq_of_mul, inv_mul_cancel
-/
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  rw [← inv_mul_cancel a⁻¹]; rw [inv_eq_of_mul (inv_mul_cancel a)]

@[to_additive (attr := simp) sub_self]
/--
theorem `div_self'` / 定理 `div_self'`

English:
theorem div_self'
  given: (a : G)
  statement: a / a = 1
  proof: by rw [div_eq_mul_inv, mul_inv_cancel a]

@[to_additive (attr := simp)]

中文:
定理 div_self'
  条件: (a : G)
  结论: a / a = 1
  证明: by rw [div_eq_mul_inv, mul_inv_cancel a]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, mul_inv_cancel
-/
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_inv_cancel a]

@[to_additive (attr := simp)]
/--
theorem `inv_mul_cancel_left` / 定理 `inv_mul_cancel_left`

English:
theorem inv_mul_cancel_left
  given: (a b : G)
  statement: a⁻¹ * (a * b) = b
  proof: by
  rw [← mul_assoc]; rw [inv_mul_cancel]; rw [one_mul]

@[to_additive (attr := simp)]

中文:
定理 inv_mul_cancel_left
  条件: (a b : G)
  结论: a⁻¹ * (a * b) = b
  证明: by
  rw [← mul_assoc]; rw [inv_mul_cancel]; rw [one_mul]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul_cancel, mul_assoc, one_mul
-/
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc]; rw [inv_mul_cancel]; rw [one_mul]

@[to_additive (attr := simp)]
/--
theorem `mul_inv_cancel_left` / 定理 `mul_inv_cancel_left`

English:
theorem mul_inv_cancel_left
  given: (a b : G)
  statement: a * (a⁻¹ * b) = b
  proof: by
  rw [← mul_assoc]; rw [mul_inv_cancel]; rw [one_mul]

@[to_additive (attr := simp)]

中文:
定理 mul_inv_cancel_left
  条件: (a b : G)
  结论: a * (a⁻¹ * b) = b
  证明: by
  rw [← mul_assoc]; rw [mul_inv_cancel]; rw [one_mul]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc, mul_inv_cancel, one_mul
-/
theorem mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b := by
  rw [← mul_assoc]; rw [mul_inv_cancel]; rw [one_mul]

@[to_additive (attr := simp)]
/--
theorem `mul_inv_cancel_right` / 定理 `mul_inv_cancel_right`

English:
theorem mul_inv_cancel_right
  given: (a b : G)
  statement: a * b * b⁻¹ = a
  proof: by
  rw [mul_assoc]; rw [mul_inv_cancel]; rw [mul_one]

@[to_additive (attr := simp)]

中文:
定理 mul_inv_cancel_right
  条件: (a b : G)
  结论: a * b * b⁻¹ = a
  证明: by
  rw [mul_assoc]; rw [mul_inv_cancel]; rw [mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: mul_assoc, mul_inv_cancel, mul_one
-/
theorem mul_inv_cancel_right (a b : G) : a * b * b⁻¹ = a := by
  rw [mul_assoc]; rw [mul_inv_cancel]; rw [mul_one]

@[to_additive (attr := simp)]
/--
theorem `mul_div_cancel_right` / 定理 `mul_div_cancel_right`

English:
theorem mul_div_cancel_right
  given: (a b : G)
  statement: a * b / b = a
  proof: by
  rw [div_eq_mul_inv]; rw [mul_inv_cancel_right a b]

@[to_additive (attr := simp)]

中文:
定理 mul_div_cancel_right
  条件: (a b : G)
  结论: a * b / b = a
  证明: by
  rw [div_eq_mul_inv]; rw [mul_inv_cancel_right a b]

@[to_additive (attr := simp)]

Depends on / 依赖: div_eq_mul_inv, mul_inv_cancel_right
-/
theorem mul_div_cancel_right (a b : G) : a * b / b = a := by
  rw [div_eq_mul_inv]; rw [mul_inv_cancel_right a b]

@[to_additive (attr := simp)]
/--
theorem `inv_mul_cancel_right` / 定理 `inv_mul_cancel_right`

English:
theorem inv_mul_cancel_right
  given: (a b : G)
  statement: a * b⁻¹ * b = a
  proof: by
  rw [mul_assoc]; rw [inv_mul_cancel]; rw [mul_one]

@[to_additive (attr := simp)]

中文:
定理 inv_mul_cancel_right
  条件: (a b : G)
  结论: a * b⁻¹ * b = a
  证明: by
  rw [mul_assoc]; rw [inv_mul_cancel]; rw [mul_one]

@[to_additive (attr := simp)]

Depends on / 依赖: inv_mul_cancel, mul_assoc, mul_one
-/
theorem inv_mul_cancel_right (a b : G) : a * b⁻¹ * b = a := by
  rw [mul_assoc]; rw [inv_mul_cancel]; rw [mul_one]

@[to_additive (attr := simp)]
/--
theorem `div_mul_cancel` / 定理 `div_mul_cancel`

English:
theorem div_mul_cancel
  given: (a b : G)
  statement: a / b * b = a
  proof: by
  rw [div_eq_mul_inv]; rw [inv_mul_cancel_right a b]

@[to_additive]

中文:
定理 div_mul_cancel
  条件: (a b : G)
  结论: a / b * b = a
  证明: by
  rw [div_eq_mul_inv]; rw [inv_mul_cancel_right a b]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, inv_mul_cancel_right
-/
theorem div_mul_cancel (a b : G) : a / b * b = a := by
  rw [div_eq_mul_inv]; rw [inv_mul_cancel_right a b]

@[to_additive]
instance (priority := 100) Group.toDivisionMonoid : DivisionMonoid G where
  inv_inv a := by exact inv_eq_of_mul (inv_mul_cancel a)
  mul_inv_rev a b := by
    apply inv_eq_of_mul
    rw [mul_assoc]; rw [mul_inv_cancel_left]; rw [mul_inv_cancel]
  inv_eq_of_mul _ _ := by exact inv_eq_of_mul

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) Group.toCancelMonoid : CancelMonoid G where
  mul_right_cancel := fun a b c h => by
    rw [← mul_inv_cancel_right b a]; rw [show b * a = c * a from h]; rw [mul_inv_cancel_right]
  mul_left_cancel := fun a {b c} h => by
    rw [← inv_mul_cancel_left a b]; rw [show a * b = a * c from h]; rw [inv_mul_cancel_left]

end Group

/--
Definition of `AddCommGroup` / `AddCommGroup` 的定义

English:
class AddCommGroup
  parameters: (G : Type u)
  extends: AddGroup G, AddCommMonoid G
  (no additional axioms)

中文:
类 AddCommGroup
  参数: (G : 类型u)
  继承: AddGroup G, AddCommMonoid G
  (无附加公理)
-/
class AddCommGroup (G : Type u) extends AddGroup G, AddCommMonoid G

/-- A commutative group is a group with commutative `(*)`. -/
-- There is intentionally no `IsMulCommutative` for `CommGroup` instance for performance reasons.
@[to_additive (attr := wikidata Q181296)]
/--
Definition of `CommGroup` / `CommGroup` 的定义

English:
class CommGroup
  parameters: (G : Type u)
  extends: Group G, CommMonoid G
  (no additional axioms)

中文:
类 CommGroup
  参数: (G : 类型u)
  继承: Group G, CommMonoid G
  (无附加公理)
-/
class CommGroup (G : Type u) extends Group G, CommMonoid G

section CommGroup

variable [CommGroup G]

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toCancelCommMonoid : CancelCommMonoid G :=
  { ‹CommGroup G›, Group.toCancelMonoid with }

-- see Note [lower instance priority]
@[to_additive]
instance (priority := 100) CommGroup.toDivisionCommMonoid : DivisionCommMonoid G :=
  { ‹CommGroup G›, Group.toDivisionMonoid with }

/--
lemma `inv_mul_cancel_comm` / 引理 `inv_mul_cancel_comm`

English:
lemma inv_mul_cancel_comm
  given: (a b : G)
  statement: a⁻¹ * b * a = b
  proof: by
  rw [mul_comm]; rw [mul_inv_cancel_left]

@[to_additive (attr := simp)]

中文:
引理 inv_mul_cancel_comm
  条件: (a b : G)
  结论: a⁻¹ * b * a = b
  证明: by
  rw [mul_comm]; rw [mul_inv_cancel_left]

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma inv_mul_cancel_comm (a b : G) : a⁻¹ * b * a = b := by
  rw [mul_comm]; rw [mul_inv_cancel_left]

@[to_additive (attr := simp)]
/--
lemma `mul_inv_cancel_comm` / 引理 `mul_inv_cancel_comm`

English:
lemma mul_inv_cancel_comm
  given: (a b : G)
  statement: a * b * a⁻¹ = b
  proof: by rw [mul_comm, inv_mul_cancel_left]

中文:
引理 mul_inv_cancel_comm
  条件: (a b : G)
  结论: a * b * a⁻¹ = b
  证明: by rw [mul_comm, inv_mul_cancel_left]

Depends on / 依赖: inv_mul_cancel_left, mul_comm
-/
lemma mul_inv_cancel_comm (a b : G) : a * b * a⁻¹ = b := by rw [mul_comm, inv_mul_cancel_left]

/--
lemma `inv_mul_cancel_comm_assoc` / 引理 `inv_mul_cancel_comm_assoc`

English:
lemma inv_mul_cancel_comm_assoc
  given: (a b : G)
  statement: a⁻¹ * (b * a) = b
  proof: by
  rw [mul_comm]; rw [mul_inv_cancel_right]

中文:
引理 inv_mul_cancel_comm_assoc
  条件: (a b : G)
  结论: a⁻¹ * (b * a) = b
  证明: by
  rw [mul_comm]; rw [mul_inv_cancel_right]
-/
@[to_additive (attr := simp)] lemma inv_mul_cancel_comm_assoc (a b : G) : a⁻¹ * (b * a) = b := by
  rw [mul_comm]; rw [mul_inv_cancel_right]

/--
lemma `mul_inv_cancel_comm_assoc` / 引理 `mul_inv_cancel_comm_assoc`

English:
lemma mul_inv_cancel_comm_assoc
  given: (a b : G)
  statement: a * (b * a⁻¹) = b
  proof: by
  rw [mul_comm]; rw [inv_mul_cancel_right]

中文:
引理 mul_inv_cancel_comm_assoc
  条件: (a b : G)
  结论: a * (b * a⁻¹) = b
  证明: by
  rw [mul_comm]; rw [inv_mul_cancel_right]
-/
@[to_additive (attr := simp)] lemma mul_inv_cancel_comm_assoc (a b : G) : a * (b * a⁻¹) = b := by
  rw [mul_comm]; rw [inv_mul_cancel_right]

end CommGroup

namespace IsMulCommutative

/-- A magma which `IsMulCommutative` is a `CommMagma`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- An additive magma which `IsMulCommutative` is a `AddCommMagma`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [Mul M] [IsMulCommutative M] : CommMagma M where
  mul_comm := mul_comm'

/-- A `Semigroup` which `IsMulCommutative` is a `CommSemigroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- An `AddSemigroup` which `IsMulCommutative` is a `AddCommSemigroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [Semigroup M] [IsMulCommutative M] :
    CommSemigroup M where

/-- A `Monoid` which `IsMulCommutative` is a `CommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- A `AddMonoid` which `IsMulCommutative` is a `AddCommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [Monoid M] [IsMulCommutative M] :
    CommMonoid M where

/-- A `DivisionMonoid` which `IsMulCommutative` is a `DivisionCommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- A `SubtractionMonoid` which `IsMulCommutative` is a `SubtractionCommMonoid`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {M : Type*} [DivisionMonoid M] [IsMulCommutative M] :
    DivisionCommMonoid M where

/-- A `Group` which `IsMulCommutative` is a `CommGroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/
@[to_additive
/-- An `AddGroup` which `IsMulCommutative` is a `AddCommGroup`.

This is primarily used to deduce the bundled version from the unbundled one for commutative
subobjects in a noncommutative ambient type. As such this is only available inside the
`IsMulCommutative` scope so as to avoid deleterious effects to type class synthesis for bundled
commutativity.

See note [commutative subobjects]. -/ ]
scoped instance (priority := 50) {G : Type*} [Group G] [IsMulCommutative G] :
    CommGroup G where

end IsMulCommutative

/-! We initialize all projections for `@[simps]` here, so that we don't have to do it in later
files.

Note: the lemmas generated for the `npow`/`zpow` projections will *not* apply to `x ^ y`, since the
argument order of these projections doesn't match the argument order of `^`.
The `nsmul`/`zsmul` lemmas will be correct. -/
initialize_simps_projections Semigroup
initialize_simps_projections AddSemigroup
initialize_simps_projections CommSemigroup
initialize_simps_projections AddCommSemigroup
initialize_simps_projections LeftCancelSemigroup
initialize_simps_projections AddLeftCancelSemigroup
initialize_simps_projections RightCancelSemigroup
initialize_simps_projections AddRightCancelSemigroup
initialize_simps_projections Monoid
initialize_simps_projections AddMonoid
initialize_simps_projections CommMonoid
initialize_simps_projections AddCommMonoid
initialize_simps_projections LeftCancelMonoid
initialize_simps_projections AddLeftCancelMonoid
initialize_simps_projections RightCancelMonoid
initialize_simps_projections AddRightCancelMonoid
initialize_simps_projections CancelMonoid
initialize_simps_projections AddCancelMonoid
initialize_simps_projections CancelCommMonoid
initialize_simps_projections AddCancelCommMonoid
initialize_simps_projections DivInvMonoid
initialize_simps_projections SubNegMonoid
initialize_simps_projections DivInvOneMonoid
initialize_simps_projections SubNegZeroMonoid
initialize_simps_projections DivisionMonoid
initialize_simps_projections SubtractionMonoid
initialize_simps_projections DivisionCommMonoid
initialize_simps_projections SubtractionCommMonoid
initialize_simps_projections Group
initialize_simps_projections AddGroup
initialize_simps_projections CommGroup
initialize_simps_projections AddCommGroup
