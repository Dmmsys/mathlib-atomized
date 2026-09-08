/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang, Fangming Li
-/
module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Order.Antidiag.Prod

/-!
# Internally graded rings and algebras

This module provides `DirectSum.GSemiring` and `DirectSum.GCommSemiring` instances for a collection
of subobjects `A` when a `SetLike.GradedMonoid` instance is available:

* `SetLike.gnonUnitalNonAssocSemiring`
* `SetLike.gsemiring`
* `SetLike.gcommSemiring`

With these instances in place, it provides the bundled canonical maps out of a direct sum of
subobjects into their carrier type:

* `DirectSum.coeRingHom` (a `RingHom` version of `DirectSum.coeAddMonoidHom`)
* `DirectSum.coeAlgHom` (an `AlgHom` version of `DirectSum.coeLinearMap`)

Strictly the definitions in this file are not sufficient to fully define an "internal" direct sum;
to represent this case, `(h : DirectSum.IsInternal A) [SetLike.GradedMonoid A]` is
needed. In the future there will likely be a data-carrying, constructive, typeclass version of
`DirectSum.IsInternal` for providing an explicit decomposition function.

When `iSupIndep (Set.range A)` (a weaker condition than
`DirectSum.IsInternal A`), these provide a grading of `⨆ i, A i`, and the
mapping `⨁ i, A i →+ ⨆ i, A i` can be obtained as
`DirectSum.toAddMonoid (fun i ↦ AddSubmonoid.inclusion <| le_iSup A i)`.

This file also provides some extra structure on `A 0`, namely:
* `SetLike.GradeZero.subsemiring`, which leads to
  * `SetLike.GradeZero.instSemiring`
  * `SetLike.GradeZero.instCommSemiring`
* `SetLike.GradeZero.subring`, which leads to
  * `SetLike.GradeZero.instRing`
  * `SetLike.GradeZero.instCommRing`
* `SetLike.GradeZero.subalgebra`, which leads to
  * `SetLike.GradeZero.instAlgebra`

## Tags

internally graded ring
-/

@[expose] public section


open DirectSum

variable {ι : Type*} {σ S R : Type*}

/-
**SetLike.algebraMap_mem_graded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.algebraMap_mem_graded [Zero ι] [CommSemiring S] [Semiring R] [Alge
bra S R] (A : ι -> Submodule S R) [SetLike.GradedOne A] (s : S) : algebraMap S R
 s in A 0
参数：A : ι -> Submodule S R；s : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `SetLike.one_mem_graded`：SetLike.one_mem_graded {S : Type*} [SetLike S R]
 [One R] [Zero ι] (A : ι -> S) [SetLike.GradedOne A] : (1 : R) in A 0
-/
theorem SetLike.algebraMap_mem_graded [Zero ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedOne A] (s : S) : algebraMap S R s ∈ A 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (A 0).smul_mem s <| SetLike.one_mem_graded _
/-
**SetLike.natCast_mem_graded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.natCast_mem_graded [Zero ι] [AddMonoidWithOne R] [SetLike σ R] [Ad
dSubmonoidClass σ R] (A : ι -> σ) [SetLike.GradedOne A] (n : Nat) : (n : R) in A
 0
参数：A : ι -> σ；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SetLike.one_mem_graded`：SetLike.one_mem_graded {S : Type*} [SetLike S R]
 [One R] [Zero ι] (A : ι -> S) [SetLike.GradedOne A] : (1 : R) in A 0
-/
theorem SetLike.natCast_mem_graded [Zero ι] [AddMonoidWithOne R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι → σ) [SetLike.GradedOne A] (n : ℕ) : (n : R) ∈ A 0 := by
  induction n with
  | zero =>
    rw [Nat.cast_zero]
    exact zero_mem (A 0)
  | succ _ n_ih =>
    rw [Nat.cast_succ]
    exact add_mem n_ih (SetLike.one_mem_graded _)
/-
**SetLike.intCast_mem_graded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.intCast_mem_graded [Zero ι] [AddGroupWithOne R] [SetLike σ R] [Add
SubgroupClass σ R] (A : ι -> σ) [SetLike.GradedOne A] (z : Int) : (z : R) in A 0
参数：A : ι -> σ；z : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_eq_natCast`：∀ (n : ℕ), Int.ofNat n = ↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `SetLike.natCast_mem_graded`：SetLike.natCast_mem_graded [Zero ι] [AddMono
idWithOne R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι -> σ) [SetLike.GradedO
ne A] (n : Nat) …
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_negSucc`：cast_negSucc (n : Nat) : (-[n+1] : R) = -(n + 1 : Nat)
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
-/
theorem SetLike.intCast_mem_graded [Zero ι] [AddGroupWithOne R] [SetLike σ R]
    [AddSubgroupClass σ R] (A : ι → σ) [SetLike.GradedOne A] (z : ℤ) : (z : R) ∈ A 0 := by
  cases z
  · rw [Int.ofNat_eq_natCast, Int.cast_natCast]
    exact SetLike.natCast_mem_graded _ _
  · rw [Int.cast_negSucc]
    exact neg_mem (SetLike.natCast_mem_graded _ _)

section DirectSum

variable [DecidableEq ι]

/-! #### From `AddSubmonoid`s and `AddSubgroup`s -/


namespace SetLike

/-- Build a `DirectSum.GNonUnitalNonAssocSemiring` instance for a collection of additive
submonoids. -/
/-
**SetLike.gnonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
形式化陈述：gnonUnitalNonAssocSemiring [Add ι] [NonUnitalNonAssocSemiring R] [SetLike 
σ R] [AddSubmonoidClass σ R] (A : ι -> σ) [SetLike.GradedMul A] : DirectSum.GNon
UnitalNonAssocSemiring fun i => A i where mul_zero _
参数：A : ι -> σ。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `DirectSum.GNonUnitalNonAssocSemiring` instance for a collection of addi
tive
submonoids.
-/
instance gnonUnitalNonAssocSemiring [Add ι] [NonUnitalNonAssocSemiring R] [SetLike σ R]
    [AddSubmonoidClass σ R] (A : ι → σ) [SetLike.GradedMul A] :
    DirectSum.GNonUnitalNonAssocSemiring fun i => A i where
  mul_zero _ := Subtype.ext (mul_zero _)
  zero_mul _ := Subtype.ext (zero_mul _)
  mul_add _ _ _ := Subtype.ext (mul_add _ _ _)
  add_mul _ _ _ := Subtype.ext (add_mul _ _ _)

/-- Build a `DirectSum.GSemiring` instance for a collection of additive submonoids. -/
/-
**SetLike.gsemiring** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
形式化陈述：gsemiring [AddMonoid ι] [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R]
 (A : ι -> σ) [SetLike.GradedMonoid A] : DirectSum.GSemiring fun i => A i where 
natCast n
参数：A : ι -> σ。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `DirectSum.GSemiring` instance for a collection of additive submonoids.
-/
instance gsemiring [AddMonoid ι] [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GSemiring fun i => A i where
  natCast n := ⟨n, SetLike.natCast_mem_graded _ _⟩
  natCast_zero := Subtype.ext Nat.cast_zero
  natCast_succ n := Subtype.ext (Nat.cast_succ n)

/-- Build a `DirectSum.GCommSemiring` instance for a collection of additive submonoids. -/
/-
**SetLike.gcommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `SetLike`。
形式化陈述：{ι : Type u_1} →   {σ : Type u_2} →     {R : Type u_4} →       [inst : Add
CommMonoid ι] →         [inst_1 : CommSemiring R] →           [inst_2 : SetLike 
σ R] →             [inst_3 : AddSubmonoidClass σ R] →               (A : ι → σ) 
→ [SetLike.GradedMonoid A] → DirectSum.GCommSemiring fun i => ↥(A i)
参数：A : ι → σ；A i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `DirectSum.GCommSemiring` instance for a collection of additive submonoi
ds.
-/
instance gcommSemiring [AddCommMonoid ι] [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]
    (A : ι → σ) [SetLike.GradedMonoid A] : DirectSum.GCommSemiring fun i => A i where

/-- Build a `DirectSum.GRing` instance for a collection of additive subgroups. -/
/-
**SetLike.gring** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
形式化陈述：gring [AddMonoid ι] [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι -
> σ) [SetLike.GradedMonoid A] : DirectSum.GRing fun i => A i where intCast z
参数：A : ι -> σ。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `DirectSum.GRing` instance for a collection of additive subgroups.
-/
instance gring [AddMonoid ι] [Ring R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GRing fun i => A i where
  intCast z := ⟨z, SetLike.intCast_mem_graded _ _⟩
  intCast_ofNat n := Subtype.ext <| Int.cast_natCast n
  intCast_negSucc_ofNat n := Subtype.ext <| Int.cast_negSucc n

/-- Build a `DirectSum.GCommRing` instance for a collection of additive submonoids. -/
/-
**SetLike.gcommRing** 是 Mathlib 中的一个定义，位于命名空间 `SetLike`。
形式化陈述：{ι : Type u_1} →   {σ : Type u_2} →     {R : Type u_4} →       [inst : Add
CommMonoid ι] →         [inst_1 : CommRing R] →           [inst_2 : SetLike σ R]
 →             [inst_3 : AddSubgroupClass σ R] →               (A : ι → σ) → [Se
tLike.GradedMonoid A] → DirectSum.GCommRing fun i => ↥(A i)
参数：A : ι → σ；A i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `DirectSum.GCommRing` instance for a collection of additive submonoids.
-/
instance gcommRing [AddCommMonoid ι] [CommRing R] [SetLike σ R] [AddSubgroupClass σ R] (A : ι → σ)
    [SetLike.GradedMonoid A] : DirectSum.GCommRing fun i => A i where

end SetLike

namespace DirectSum

section coe

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)

/-- The canonical ring isomorphism between `⨁ i, A i` and `R` -/
/-
**DirectSum.coeRingHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：coeRingHom [AddMonoid ι] [SetLike.GradedMonoid A] : (⨁ i, A i) ->+* R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical ring isomorphism between `⨁ i, A i` and `R`
-/
def coeRingHom [AddMonoid ι] [SetLike.GradedMonoid A] : (⨁ i, A i) →+* R :=
  DirectSum.toSemiring (fun i => AddSubmonoidClass.subtype (A i)) rfl fun _ _ => rfl

/-- The canonical ring isomorphism between `⨁ i, A i` and `R` -/
@[simp]
/-
**DirectSum.coeRingHom_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coeRingHom_of [AddMonoid ι] [SetLike.GradedMonoid A] (i : ι) (x : A i) : (
coeRingHom A : _ ->+* R) (of (fun i => A i) i x) = x
参数：i : ι；x : A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toSemiring_of`：toSemiring_of (f : forall i, A i ->+ R) (hone h
mul) (i : ι) (x : A i) : toSemiring f hone hmul (of _ i x) = f _ x

--- 原说明 ---
The canonical ring isomorphism between `⨁ i, A i` and `R`
-/
theorem coeRingHom_of [AddMonoid ι] [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    (coeRingHom A : _ →+* R) (of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.coe_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_mul_apply [AddMonoid ι] [SetLike.GradedMonoid A] [forall (i : ι) (x : 
A i), Decidable (x != 0)] (r r' : ⨁ i, A i) (n : ι) : ((r * r') n : R) = ∑ ij in
 r.support ×ˢ r'.support with ij.1 + ij.2 = n, (r ij.1 * r' ij.2 : R)
参数：i : ι；x : A i；x != 0；r r' : ⨁ i, A i；n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.mul_eq_sum_support_ghas_mul`：mul_eq_sum_support_ghas_mul [fora
ll (i : ι) (x : A i), Decidable (x != 0)] (a a' : ⨁ i, A i) : a * a' = ∑ ij in D
Finsupp.support a ×ˢ DFinsu…
· 使用定理 `DFinsupp.finsetSum_apply`：finsetSum_apply {α} [forall i, AddCommMonoid (
β i)] (s : Finset α) (g : α -> Π₀ i, β i) (i : ι) : (∑ a in s, g a) i = ∑ a in s
, g a i
· 使用定理 `AddSubmonoidClass.coe_finsetSum`：∀ {B : Type u_3} {S : B} {ι : Type u_4}
 {M : Type u_5} [inst : AddCommMonoid M] [inst_1 : SetLike B M]   [inst_2 : AddS
ubmonoidClass B M] (f…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectSum.coe_of_apply`：coe_of_apply {M S : Type*} [DecidableEq ι] [AddC
ommMonoid M] [SetLike S M] [AddSubmonoidClass S M] {A : ι -> S} (i j : ι) (x : A
 i) : (of (f…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_mul_apply [AddMonoid ι] [SetLike.GradedMonoid A]
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) =
      ∑ ij ∈ r.support ×ˢ r'.support with ij.1 + ij.2 = n, (r ij.1 * r' ij.2 : R) := by
  rw [mul_eq_sum_support_ghas_mul, DFinsupp.finsetSum_apply, AddSubmonoidClass.coe_finsetSum]
  simp_rw [coe_of_apply, apply_ite, ZeroMemClass.coe_zero, ← Finset.sum_filter, SetLike.coe_gMul]

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.coe_mul_apply_eq_dfinsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_mul_apply_eq_dfinsuppSum [AddMonoid ι] [SetLike.GradedMonoid A] [foral
l (i : ι) (x : A i), Decidable (x != 0)] (r r' : ⨁ i, A i) (n : ι) : ((r * r') n
 : R) = r.sum fun i ri => r'.sum fun j rj => if i + j = n then (ri * rj : R) els
e 0
参数：i : ι；x : A i；x != 0；r r' : ⨁ i, A i；n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.mul_eq_dfinsuppSum`：mul_eq_dfinsuppSum [forall (i : ι) (x : A 
i), Decidable (x != 0)] (a a' : ⨁ i, A i) : a * a' = a.sum fun _ ai => a'.sum fu
n _ aj => DirectSu…
· 使用定理 `DFinsupp.sum_apply`：sum_apply {ι} {β : ι -> Type v} {ι₁ : Type u₁} [Deci
dableEq ι₁] {β₁ : ι₁ -> Type v₁} [forall i₁, Zero (β₁ i₁)] [forall (i) (x : β₁ i
), Decid…
· 使用定理 `DFinsupp.sum.eq_1`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i) →
 Decida…
· 使用定理 `AddSubmonoidClass.coe_finsetSum`：∀ {B : Type u_3} {S : B} {ι : Type u_4}
 {M : Type u_5} [inst : AddCommMonoid M] [inst_1 : SetLike B M]   [inst_2 : AddS
ubmonoidClass B M] (f…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DirectSum.of_eq_of_ne`：of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (o
f _ i x) j = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem coe_mul_apply_eq_dfinsuppSum [AddMonoid ι] [SetLike.GradedMonoid A]
    [∀ (i : ι) (x : A i), Decidable (x ≠ 0)] (r r' : ⨁ i, A i) (n : ι) :
    ((r * r') n : R) = r.sum fun i ri => r'.sum fun j rj => if i + j = n then (ri * rj : R)
      else 0 := by
  rw [mul_eq_dfinsuppSum]
  iterate 2 rw [DFinsupp.sum_apply, DFinsupp.sum, AddSubmonoidClass.coe_finsetSum]; congr; ext
  dsimp only
  split_ifs with h
  · subst h
    rw [of_eq_same]
    rfl
  · rw [of_eq_of_ne _ _ _ (Ne.symm h)]
    rfl

set_option backward.isDefEq.respectTransparency false in
open Finset in
/-
**DirectSum.coe_mul_apply_eq_sum_antidiagonal** 是 Mathlib 中的一个定理，位于命名空间 `DirectS
um`。
形式化陈述：coe_mul_apply_eq_sum_antidiagonal [AddMonoid ι] [HasAntidiagonal ι] [SetLi
ke.GradedMonoid A] (r r' : ⨁ i, A i) (n : ι) : (r * r') n = ∑ ij in antidiagonal
 n, (r ij.1 : R) * r' ij.2
参数：r r' : ⨁ i, A i；n : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.coe_mul_apply`：coe_mul_apply [AddMonoid ι] [SetLike.GradedMono
id A] [forall (i : ι) (x : A i), Decidable (x != 0)] (r r' : ⨁ i, A i) (n : ι) :
 ((r * r') n …
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
theorem coe_mul_apply_eq_sum_antidiagonal [AddMonoid ι] [HasAntidiagonal ι]
    [SetLike.GradedMonoid A] (r r' : ⨁ i, A i) (n : ι) :
    (r * r') n = ∑ ij ∈ antidiagonal n, (r ij.1 : R) * r' ij.2 := by
  classical
  rw [coe_mul_apply]
  apply Finset.sum_subset (fun _ ↦ by simp)
  aesop (erase simp not_and) (add simp not_and_or)

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.coe_of_mul_apply_aux** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_of_mul_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A
 i) (r' : ⨁ i, A i) {j n : ι} (H : forall x : ι, i + x = n ↔ x = j) : ((of (fun 
i => A i) i r * r') n : R) = r * r' j
参数：r : A i；r' : ⨁ i, A i；H : forall x : ι, i + x = n ↔ x = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.coe_mul_apply_eq_dfinsuppSum`：coe_mul_apply_eq_dfinsuppSum [Ad
dMonoid ι] [SetLike.GradedMonoid A] [forall (i : ι) (x : A i), Decidable (x != 0
)] (r r' : ⨁ i, A i) (n : ι)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.sum_single_index`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x 
: β i) → Decida…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.sum.congr_simp`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} {i
nst : DecidableEq ι} [inst_1 : DecidableEq ι]   [inst_2 : (i : ι) → Zero (β i)] 
{inst_3 : (i …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `DFinsupp.sum_zero`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → AddCommMonoid (β i)]   [inst_2 : (i : ι) → (x
 : β i)…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.notMem_support_iff`：notMem_support_iff {f : Π₀ i, β i} {i : ι} 
: i ∉ f.support ↔ f i = 0
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem coe_of_mul_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) {j n : ι} (H : ∀ x : ι, i + x = n ↔ x = j) :
    ((of (fun i => A i) i r * r') n : R) = r * r' j := by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.notMem_support_iff.mp h, ZeroMemClass.coe_zero, mul_zero]

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.coe_mul_of_apply_aux** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_mul_of_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
 {i : ι} (r' : A i) {j n : ι} (H : forall x : ι, x + i = n ↔ x = j) : ((r * of (
fun i => A i) i r') n : R) = r j * r'
参数：r : ⨁ i, A i；r' : A i；H : forall x : ι, x + i = n ↔ x = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.coe_mul_apply_eq_dfinsuppSum`：coe_mul_apply_eq_dfinsuppSum [Ad
dMonoid ι] [SetLike.GradedMonoid A] [forall (i : ι) (x : A i), Decidable (x != 0
)] (r r' : ⨁ i, A i) (n : ι)…
· 使用定理 `DFinsupp.sum_comm`：∀ {γ : Type w} {ι₁ : Type u_3} {ι₂ : Type u_4} {β₁ : 
ι₁ → Type u_1} {β₂ : ι₂ → Type u_2} [inst : DecidableEq ι₁]   [inst_1 : Decidabl
eEq ι₂]…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.sum_single_index`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x 
: β i) → Decida…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.sum.congr_simp`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} {i
nst : DecidableEq ι} [inst_1 : DecidableEq ι]   [inst_2 : (i : ι) → Zero (β i)] 
{inst_3 : (i …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `DFinsupp.sum_zero`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → AddCommMonoid (β i)]   [inst_2 : (i : ι) → (x
 : β i)…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFinsupp.notMem_support_iff`：notMem_support_iff {f : Π₀ i, β i} {i : ι} 
: i ∉ f.support ↔ f i = 0
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem coe_mul_of_apply_aux [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i) {i : ι}
    (r' : A i) {j n : ι} (H : ∀ x : ι, x + i = n ↔ x = j) :
    ((r * of (fun i => A i) i r') n : R) = r j * r' := by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum, DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    simp_rw [DFinsupp.sum, H, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    rw [DFinsupp.notMem_support_iff.mp h, ZeroMemClass.coe_zero, zero_mul]
/-
**DirectSum.coe_of_mul_apply_add** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_of_mul_apply_add [AddLeftCancelMonoid ι] [SetLike.GradedMonoid A] {i :
 ι} (r : A i) (r' : ⨁ i, A i) (j : ι) : ((of (fun i => A i) i r * r') (i + j) : 
R) = r * r' j
参数：r : A i；r' : ⨁ i, A i；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.coe_of_mul_apply_aux`：coe_of_mul_apply_aux [AddMonoid ι] [SetL
ike.GradedMonoid A] {i : ι} (r : A i) (r' : ⨁ i, A i) {j n : ι} (H : forall x : 
ι, i + x = n ↔ x = j…
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
theorem coe_of_mul_apply_add [AddLeftCancelMonoid ι] [SetLike.GradedMonoid A] {i : ι} (r : A i)
    (r' : ⨁ i, A i) (j : ι) : ((of (fun i => A i) i r * r') (i + j) : R) = r * r' j :=
  coe_of_mul_apply_aux _ _ _ fun _x => ⟨fun h => add_left_cancel h, fun h => h ▸ rfl⟩
/-
**DirectSum.coe_mul_of_apply_add** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_mul_of_apply_add [AddRightCancelMonoid ι] [SetLike.GradedMonoid A] (r 
: ⨁ i, A i) {i : ι} (r' : A i) (j : ι) : ((r * of (fun i => A i) i r') (j + i) :
 R) = r j * r'
参数：r : ⨁ i, A i；r' : A i；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.coe_mul_of_apply_aux`：coe_mul_of_apply_aux [AddMonoid ι] [SetL
ike.GradedMonoid A] (r : ⨁ i, A i) {i : ι} (r' : A i) {j n : ι} (H : forall x : 
ι, x + i = n ↔ x = j…
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
theorem coe_mul_of_apply_add [AddRightCancelMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
    {i : ι} (r' : A i) (j : ι) : ((r * of (fun i => A i) i r') (j + i) : R) = r j * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => ⟨fun h => add_right_cancel h, fun h => h ▸ rfl⟩
/-
**DirectSum.coe_of_mul_apply_of_mem_zero** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_of_mul_apply_of_mem_zero [AddMonoid ι] [SetLike.GradedMonoid A] (r : A
 0) (r' : ⨁ i, A i) (j : ι) : ((of (fun i => A i) 0 r * r') j : R) = r * r' j
参数：r : A 0；r' : ⨁ i, A i；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.coe_of_mul_apply_aux`：coe_of_mul_apply_aux [AddMonoid ι] [SetL
ike.GradedMonoid A] {i : ι} (r : A i) (r' : ⨁ i, A i) {j n : ι} (H : forall x : 
ι, i + x = n ↔ x = j…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_of_mul_apply_of_mem_zero [AddMonoid ι] [SetLike.GradedMonoid A] (r : A 0)
    (r' : ⨁ i, A i) (j : ι) : ((of (fun i => A i) 0 r * r') j : R) = r * r' j :=
  coe_of_mul_apply_aux _ _ _ fun _x => by rw [zero_add]
/-
**DirectSum.coe_mul_of_apply_of_mem_zero** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_mul_of_apply_of_mem_zero [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁
 i, A i) (r' : A 0) (j : ι) : ((r * of (fun i => A i) 0 r') j : R) = r j * r'
参数：r : ⨁ i, A i；r' : A 0；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.coe_mul_of_apply_aux`：coe_mul_of_apply_aux [AddMonoid ι] [SetL
ike.GradedMonoid A] (r : ⨁ i, A i) {i : ι} (r' : A i) {j n : ι} (H : forall x : 
ι, x + i = n ↔ x = j…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_mul_of_apply_of_mem_zero [AddMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i)
    (r' : A 0) (j : ι) : ((r * of (fun i => A i) 0 r') j : R) = r j * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => by rw [add_zero]

end coe

section CanonicallyOrderedAddCommMonoid

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R] (A : ι → σ)
variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι] [SetLike.GradedMonoid A]

set_option backward.isDefEq.respectTransparency.types false in
/-
**DirectSum.coe_of_mul_apply_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_of_mul_apply_of_not_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : 
¬i <= n) : ((of (fun i => A i) i r * r') n : R) = 0
参数：r : A i；r' : ⨁ i, A i；n : ι；h : ¬i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.coe_mul_apply_eq_dfinsuppSum`：coe_mul_apply_eq_dfinsuppSum [Ad
dMonoid ι] [SetLike.GradedMonoid A] [forall (i : ι) (x : A i), Decidable (x != 0
)] (r r' : ⨁ i, A i) (n : ι)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.sum_single_index`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x 
: β i) → Decida…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.sum.congr_simp`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} {i
nst : DecidableEq ι} [inst_1 : DecidableEq ι]   [inst_2 : (i : ι) → Zero (β i)] 
{inst_3 : (i …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `DFinsupp.sum_zero`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → AddCommMonoid (β i)]   [inst_2 : (i : ι) → (x
 : β i)…
· 使用定理 `DFinsupp.sum.eq_1`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i) →
 Decida…
· 使用定理 `Finset.sum_ite_of_false`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} 
[inst : AddCommMonoid M] {p : ι → Prop} [inst_1 : DecidablePred p],   (∀ x ∈ s, 
¬p x) → ∀ (f …
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
-/
theorem coe_of_mul_apply_of_not_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : ¬i ≤ n) :
    ((of (fun i => A i) i r * r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, zero_mul, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_right i x).trans_eq H)

set_option backward.isDefEq.respectTransparency.types false in
/-
**DirectSum.coe_mul_of_apply_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_mul_of_apply_of_not_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : 
¬i <= n) : ((r * of (fun i => A i) i r') n : R) = 0
参数：r : ⨁ i, A i；r' : A i；n : ι；h : ¬i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.coe_mul_apply_eq_dfinsuppSum`：coe_mul_apply_eq_dfinsuppSum [Ad
dMonoid ι] [SetLike.GradedMonoid A] [forall (i : ι) (x : A i), Decidable (x != 0
)] (r r' : ⨁ i, A i) (n : ι)…
· 使用定理 `DFinsupp.sum_comm`：∀ {γ : Type w} {ι₁ : Type u_3} {ι₂ : Type u_4} {β₁ : 
ι₁ → Type u_1} {β₂ : ι₂ → Type u_2} [inst : DecidableEq ι₁]   [inst_1 : Decidabl
eEq ι₂]…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DFinsupp.sum_single_index`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} 
[inst : DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x 
: β i) → Decida…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DFinsupp.sum.congr_simp`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} {i
nst : DecidableEq ι} [inst_1 : DecidableEq ι]   [inst_2 : (i : ι) → Zero (β i)] 
{inst_3 : (i …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `DFinsupp.sum_zero`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → AddCommMonoid (β i)]   [inst_2 : (i : ι) → (x
 : β i)…
· 使用定理 `DFinsupp.sum.eq_1`：∀ {ι : Type u} {γ : Type w} {β : ι → Type v} [inst : 
DecidableEq ι] [inst_1 : (i : ι) → Zero (β i)]   [inst_2 : (i : ι) → (x : β i) →
 Decida…
· 使用定理 `Finset.sum_ite_of_false`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} 
[inst : AddCommMonoid M] {p : ι → Prop} [inst_1 : DecidablePred p],   (∀ x ∈ s, 
¬p x) → ∀ (f …
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
-/
theorem coe_mul_of_apply_of_not_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : ¬i ≤ n) :
    ((r * of (fun i => A i) i r') n : R) = 0 := by
  classical
    rw [coe_mul_apply_eq_dfinsuppSum, DFinsupp.sum_comm]
    apply (DFinsupp.sum_single_index _).trans
    swap
    · simp_rw [ZeroMemClass.coe_zero, mul_zero, ite_self]
      exact DFinsupp.sum_zero
    · rw [DFinsupp.sum, Finset.sum_ite_of_false, Finset.sum_const_zero]
      exact fun x _ H => h ((self_le_add_left i x).trans_eq H)

variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]

/-! The following two lemmas only require the same hypotheses as `eq_tsub_iff_add_eq_of_le`, but we
state them for the above typeclasses for convenience. -/

/-
**DirectSum.coe_mul_of_apply_of_le** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_mul_of_apply_of_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : i <=
 n) : ((r * of (fun i => A i) i r') n : R) = r (n - i) * r'
参数：r : ⨁ i, A i；r' : A i；n : ι；h : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.coe_mul_of_apply_aux`：coe_mul_of_apply_aux [AddMonoid ι] [SetL
ike.GradedMonoid A] (r : ⨁ i, A i) {i : ι} (r' : A i) {j n : ι} (H : forall x : 
ι, x + i = n ↔ x = j…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `eq_tsub_iff_add_eq_of_le`：eq_tsub_iff_add_eq_of_le (h : c <= b) : a = b 
- c ↔ a + c = b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α

--- 原说明 ---
The following two lemmas only require the same hypotheses as `eq_tsub_iff_add_eq
_of_le`, but we
state them for the above typeclasses for convenience.
-/
theorem coe_mul_of_apply_of_le (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) (h : i ≤ n) :
    ((r * of (fun i => A i) i r') n : R) = r (n - i) * r' :=
  coe_mul_of_apply_aux _ _ _ fun _x => (eq_tsub_iff_add_eq_of_le h).symm
/-
**DirectSum.coe_of_mul_apply_of_le** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_of_mul_apply_of_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : i <=
 n) : ((of (fun i => A i) i r * r') n : R) = r * r' (n - i)
参数：r : A i；r' : ⨁ i, A i；n : ι；h : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.coe_of_mul_apply_aux`：coe_of_mul_apply_aux [AddMonoid ι] [SetL
ike.GradedMonoid A] {i : ι} (r : A i) (r' : ⨁ i, A i) {j n : ι} (H : forall x : 
ι, i + x = n ↔ x = j…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_tsub_iff_add_eq_of_le`：eq_tsub_iff_add_eq_of_le (h : c <= b) : a = b 
- c ↔ a + c = b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_of_mul_apply_of_le {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) (h : i ≤ n) :
    ((of (fun i => A i) i r * r') n : R) = r * r' (n - i) :=
  coe_of_mul_apply_aux _ _ _ fun x => by rw [eq_tsub_iff_add_eq_of_le h, add_comm]
/-
**DirectSum.coe_mul_of_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_mul_of_apply (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [Decidable (i <
= n)] : ((r * of (fun i => A i) i r') n : R) = if i <= n then (r (n - i) : R) * 
r' else 0
参数：r : ⨁ i, A i；r' : A i；n : ι；i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `DirectSum.coe_mul_of_apply_of_le`：coe_mul_of_apply_of_le (r : ⨁ i, A i) 
{i : ι} (r' : A i) (n : ι) (h : i <= n) : ((r * of (fun i => A i) i r') n : R) =
 r (n - i) * r'
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DirectSum.coe_mul_of_apply_of_not_le`：coe_mul_of_apply_of_not_le (r : ⨁ 
i, A i) {i : ι} (r' : A i) (n : ι) (h : ¬i <= n) : ((r * of (fun i => A i) i r')
 n : R) = 0
-/
theorem coe_mul_of_apply (r : ⨁ i, A i) {i : ι} (r' : A i) (n : ι) [Decidable (i ≤ n)] :
    ((r * of (fun i => A i) i r') n : R) = if i ≤ n then (r (n - i) : R) * r' else 0 := by
  split_ifs with h
  exacts [coe_mul_of_apply_of_le _ _ _ n h, coe_mul_of_apply_of_not_le _ _ _ n h]
/-
**DirectSum.coe_of_mul_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_of_mul_apply {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [Decidable (i <
= n)] : ((of (fun i => A i) i r * r') n : R) = if i <= n then (r * r' (n - i) : 
R) else 0
参数：r : A i；r' : ⨁ i, A i；n : ι；i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `DirectSum.coe_of_mul_apply_of_le`：coe_of_mul_apply_of_le {i : ι} (r : A 
i) (r' : ⨁ i, A i) (n : ι) (h : i <= n) : ((of (fun i => A i) i r * r') n : R) =
 r * r' (n - i)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `DirectSum.coe_of_mul_apply_of_not_le`：coe_of_mul_apply_of_not_le {i : ι}
 (r : A i) (r' : ⨁ i, A i) (n : ι) (h : ¬i <= n) : ((of (fun i => A i) i r * r')
 n : R) = 0
-/
theorem coe_of_mul_apply {i : ι} (r : A i) (r' : ⨁ i, A i) (n : ι) [Decidable (i ≤ n)] :
    ((of (fun i => A i) i r * r') n : R) = if i ≤ n then (r * r' (n - i) : R) else 0 := by
  split_ifs with h
  exacts [coe_of_mul_apply_of_le _ _ _ n h, coe_of_mul_apply_of_not_le _ _ _ n h]

end CanonicallyOrderedAddCommMonoid

end DirectSum

/-! #### From `Submodule`s -/

namespace Submodule

/-- Build a `DirectSum.GAlgebra` instance for a collection of `Submodule`s. -/
/-
**Submodule.galgebra** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：galgebra [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R] (A : ι 
-> Submodule S R) [SetLike.GradedMonoid A] : DirectSum.GAlgebra S fun i => A i w
here toFun
参数：A : ι -> Submodule S R。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a `DirectSum.GAlgebra` instance for a collection of `Submodule`s.
-/
instance galgebra [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R] (A : ι → Submodule S R)
    [SetLike.GradedMonoid A] : DirectSum.GAlgebra S fun i => A i where
  toFun :=
    ((Algebra.linearMap S R).codRestrict (A 0) <| SetLike.algebraMap_mem_graded A).toAddMonoidHom
  map_one := Subtype.ext <| (algebraMap S R).map_one
  map_mul _x _y := Sigma.subtype_ext (add_zero 0).symm <| (algebraMap S R).map_mul _ _
  commutes := fun _r ⟨i, _xi⟩ =>
    Sigma.subtype_ext ((zero_add i).trans (add_zero i).symm) <| Algebra.commutes _ _
  smul_def := fun _r ⟨i, _xi⟩ => Sigma.subtype_ext (zero_add i).symm <| Algebra.smul_def _ _

@[simp]
/-
**Submodule.setLike.coe_galgebra_toFun** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.setL
ike`。
形式化陈述：∀ {S : Type u_3} {R : Type u_4} {ι : Type u_5} [inst : AddMonoid ι] [inst_
1 : CommSemiring S] [inst_2 : Semiring R]   [inst_3 : Algebra S R] (A : ι → Subm
odule S R) [inst_4 : SetLike.GradedMonoid A] (s : S),   ↑(DirectSum.GAlgebra.toF
un s) = (algebraMap S R) s
参数：A : ι → Submodule S R；s : S；DirectSum.GAlgebra.toFun s；algebraMap S R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem setLike.coe_galgebra_toFun {ι} [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (s : S) :
    (DirectSum.GAlgebra.toFun (A := fun i => A i) s) = (algebraMap S R s : R) :=
  rfl

/-- A direct sum of powers of a submodule of an algebra has a multiplicative structure. -/
/-
**Submodule.nat_power_gradedMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：nat_power_gradedMonoid [CommSemiring S] [Semiring R] [Algebra S R] (p : Su
bmodule S R) : SetLike.GradedMonoid fun i : Nat => p ^ i where one_mem
参数：p : Submodule S R。
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.one_le`：one_le {P : Submodule R A} : (1 : Submodule R A) <= P 
↔ (1 : A) in P
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Submodule.mul_mem_mul`：mul_mem_mul (hm : m in M) (hn : n in N) : m * n i
n M * N

--- 原说明 ---
A direct sum of powers of a submodule of an algebra has a multiplicative structu
re.
-/
instance nat_power_gradedMonoid [CommSemiring S] [Semiring R] [Algebra S R] (p : Submodule S R) :
    SetLike.GradedMonoid fun i : ℕ => p ^ i where
  one_mem := by
    rw [← one_le, pow_zero]
  mul_mem i j p q hp hq := by
    rw [pow_add]
    exact Submodule.mul_mem_mul hp hq

end Submodule

/-- The canonical algebra isomorphism between `⨁ i, A i` and `R`. -/
/-
**DirectSum.coeAlgHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：DirectSum.coeAlgHom [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S
 R] (A : ι -> Submodule S R) [SetLike.GradedMonoid A] : (⨁ i, A i) ->ₐ[S] R
参数：A : ι -> Submodule S R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical algebra isomorphism between `⨁ i, A i` and `R`.
-/
def DirectSum.coeAlgHom [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] : (⨁ i, A i) →ₐ[S] R :=
  DirectSum.toAlgebra S _ (fun i => (A i).subtype) rfl (fun _ _ => rfl)

/-- The supremum of submodules that form a graded monoid is a subalgebra, and equal to the range of
`DirectSum.coeAlgHom`. -/
/-
**Submodule.iSup_eq_toSubmodule_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.iSup_eq_toSubmodule_range [AddMonoid ι] [CommSemiring S] [Semiri
ng R] [Algebra S R] (A : ι -> Submodule S R) [SetLike.GradedMonoid A] : ⨆ i, A i
 = Subalgebra.toSubmodule (DirectSum.coeAlgHom A).range
参数：A : ι -> Submodule S R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.iSup_eq_range_dfinsupp_lsum`：iSup_eq_range_dfinsupp_lsum (p : 
ι -> Submodule R N) : iSup p = LinearMap.range (DFinsupp.lsum Nat fun i => (p i)
.subtype)
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe

--- 原说明 ---
The supremum of submodules that form a graded monoid is a subalgebra, and equal 
to the range of
`DirectSum.coeAlgHom`.
-/
theorem Submodule.iSup_eq_toSubmodule_range [AddMonoid ι] [CommSemiring S] [Semiring R]
    [Algebra S R] (A : ι → Submodule S R) [SetLike.GradedMonoid A] :
    ⨆ i, A i = Subalgebra.toSubmodule (DirectSum.coeAlgHom A).range :=
  (Submodule.iSup_eq_range_dfinsupp_lsum A).trans <| SetLike.coe_injective rfl

@[simp]
/-
**DirectSum.coeAlgHom_of** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：DirectSum.coeAlgHom_of [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebr
a S R] (A : ι -> Submodule S R) [SetLike.GradedMonoid A] (i : ι) (x : A i) : Dir
ectSum.coeAlgHom A (DirectSum.of (fun i => A i) i x) = x
参数：A : ι -> Submodule S R；i : ι；x : A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toSemiring_of`：toSemiring_of (f : forall i, A i ->+ R) (hone h
mul) (i : ι) (x : A i) : toSemiring f hone hmul (of _ i x) = f _ x
-/
theorem DirectSum.coeAlgHom_of [AddMonoid ι] [CommSemiring S] [Semiring R] [Algebra S R]
    (A : ι → Submodule S R) [SetLike.GradedMonoid A] (i : ι) (x : A i) :
    DirectSum.coeAlgHom A (DirectSum.of (fun i => A i) i x) = x :=
  DirectSum.toSemiring_of _ rfl (fun _ _ => rfl) _ _

end DirectSum

/-! ### Facts about grade zero -/

namespace SetLike.GradeZero

section Semiring
variable [Semiring R] [AddMonoid ι] [SetLike σ R] [AddSubmonoidClass σ R]
variable (A : ι → σ) [SetLike.GradedMonoid A]

/-- The subsemiring `A 0` of `R`. -/
/-
**SetLike.GradeZero.subsemiring** 是 Mathlib 中的一个定义，位于命名空间 `SetLike.GradeZero`。
形式化陈述：subsemiring : Subsemiring R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subsemiring `A 0` of `R`.
-/
def subsemiring : Subsemiring R where
  __ := submonoid A
  add_mem' := add_mem
  zero_mem' := zero_mem (A 0)

-- TODO: it might be expensive to unify `A` in this instance in practice
/-- The semiring `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
/-
**SetLike.GradeZero.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `SetLike.GradeZero`。
形式化陈述：instSemiring : Semiring (A 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The semiring `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A
`.
-/
instance instSemiring : Semiring (A 0) := inferInstanceAs <| Semiring (subsemiring A)
/-
**SetLike.GradeZero.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `SetLike.GradeZero`。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {R : Type u_4} [inst : Semiring R] [inst_1
 : AddMonoid ι] [inst_2 : SetLike σ R]   [inst_3 : AddSubmonoidClass σ R] (A : ι
 → σ) [inst_4 : SetLike.GradedMonoid A] (n : ℕ), ↑↑n = ↑n
参数：A : ι → σ；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_natCast (n : ℕ) : (n : A 0) = (n : R) := rfl
/-
**SetLike.GradeZero.coe_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `SetLike.GradeZero`。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {R : Type u_4} [inst : Semiring R] [inst_1
 : AddMonoid ι] [inst_2 : SetLike σ R]   [inst_3 : AddSubmonoidClass σ R] (A : ι
 → σ) [inst_4 : SetLike.GradedMonoid A] (n : ℕ) [inst_5 : n.AtLeastTwo],   ↑(OfN
at.ofNat n) = OfNat.ofNat n
参数：A : ι → σ；n : ℕ；OfNat.ofNat n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_ofNat (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : A 0) = (ofNat(n) : R) := rfl

end Semiring

section CommSemiring
variable [CommSemiring R] [AddMonoid ι] [SetLike σ R] [AddSubmonoidClass σ R]
variable (A : ι → σ) [SetLike.GradedMonoid A]

-- TODO: it might be expensive to unify `A` in this instance in practice
/-- The commutative semiring `A 0` inherited from `R` in the presence of
`SetLike.GradedMonoid A`. -/
/-
**SetLike.GradeZero.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `SetLike.GradeZer
o`。
形式化陈述：instCommSemiring : CommSemiring (A 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The commutative semiring `A 0` inherited from `R` in the presence of
`SetLike.GradedMonoid A`.
-/
instance instCommSemiring : CommSemiring (A 0) := inferInstanceAs <| CommSemiring (subsemiring A)
/-
**SetLike.GradeZero.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike.GradeZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra (A 0) R :=
  inferInstanceAs <| Algebra (SetLike.GradeZero.subsemiring A) R
/-
**SetLike.GradeZero.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `SetLike.GradeZer
o`。
形式化陈述：∀ {ι : Type u_1} {σ : Type u_2} {R : Type u_4} [inst : CommSemiring R] [in
st_1 : AddMonoid ι] [inst_2 : SetLike σ R]   [inst_3 : AddSubmonoidClass σ R] (A
 : ι → σ) [inst_4 : SetLike.GradedMonoid A] (x : ↥(A 0)),   (algebraMap (↥(A 0))
 R) x = ↑x
参数：A : ι → σ；x : ↥(A 0)；algebraMap (↥(A 0)) R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma algebraMap_apply (x : A 0) : algebraMap (A 0) R x = x := rfl

end CommSemiring

section Ring
variable [Ring R] [AddMonoid ι] [SetLike σ R] [AddSubgroupClass σ R]
variable (A : ι → σ) [SetLike.GradedMonoid A]

/-- The subring `A 0` of `R`. -/
/-
**SetLike.GradeZero.subring** 是 Mathlib 中的一个定义，位于命名空间 `SetLike.GradeZero`。
形式化陈述：subring : Subring R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subring `A 0` of `R`.
-/
def subring : Subring R where
  __ := subsemiring A
  neg_mem' := neg_mem

-- TODO: it might be expensive to unify `A` in this instance in practice
/-- The ring `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
/-
**SetLike.GradeZero.instRing** 是 Mathlib 中的一个实例，位于命名空间 `SetLike.GradeZero`。
形式化陈述：instRing : Ring (A 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`.
-/
instance instRing : Ring (A 0) := inferInstanceAs <| Ring (subring A)
/-
**SetLike.GradeZero.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `SetLike.GradeZero`。
形式化陈述：coe_intCast (z : Int) : (z : A 0) = (z : R)
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_intCast (z : ℤ) : (z : A 0) = (z : R) := rfl

end Ring

section CommRing
variable [CommRing R] [AddCommMonoid ι] [SetLike σ R] [AddSubgroupClass σ R]
variable (A : ι → σ) [SetLike.GradedMonoid A]

-- TODO: it might be expensive to unify `A` in this instance in practice
/-- The commutative ring `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
/-
**SetLike.GradeZero.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `SetLike.GradeZero`。
形式化陈述：instCommRing : CommRing (A 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The commutative ring `A 0` inherited from `R` in the presence of `SetLike.Graded
Monoid A`.
-/
instance instCommRing : CommRing (A 0) := inferInstanceAs <| CommRing (subring A)

end CommRing

section Algebra
variable [CommSemiring S] [Semiring R] [Algebra S R] [AddMonoid ι]
variable (A : ι → Submodule S R) [SetLike.GradedMonoid A]

/-- The subalgebra `A 0` of `R`. -/
/-
**SetLike.GradeZero.subalgebra** 是 Mathlib 中的一个定义，位于命名空间 `SetLike.GradeZero`。
形式化陈述：subalgebra : Subalgebra S R where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subalgebra `A 0` of `R`.
-/
def subalgebra : Subalgebra S R where
  __ := subsemiring A
  algebraMap_mem' := algebraMap_mem_graded A

-- TODO: it might be expensive to unify `A` in this instance in practice
/-- The `S`-algebra `A 0` inherited from `R` in the presence of `SetLike.GradedMonoid A`. -/
/-
**SetLike.GradeZero.instAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `SetLike.GradeZero`。
形式化陈述：instAlgebra : Algebra S (A 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `S`-algebra `A 0` inherited from `R` in the presence of `SetLike.GradedMonoi
d A`.
-/
instance instAlgebra : Algebra S (A 0) := inferInstanceAs <| Algebra S (subalgebra A)
/-
**SetLike.GradeZero.coe_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `SetLike.GradeZero`
。
形式化陈述：∀ {ι : Type u_1} {S : Type u_3} {R : Type u_4} [inst : CommSemiring S] [in
st_1 : Semiring R] [inst_2 : Algebra S R]   [inst_3 : AddMonoid ι] (A : ι → Subm
odule S R) [inst_4 : SetLike.GradedMonoid A] (s : S),   ↑((algebraMap S ↥(A 0)) 
s) = (algebraMap S R) s
参数：A : ι → Submodule S R；s : S；(algebraMap S ↥(A 0)) s；algebraMap S R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] theorem coe_algebraMap (s : S) :
    ↑(algebraMap _ (A 0) s) = algebraMap _ R s := rfl

end Algebra

end SetLike.GradeZero

section HomogeneousElement

/-
**SetLike.homogeneous_zero_submodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.homogeneous_zero_submodule [Zero ι] [Semiring S] [AddCommMonoid R]
 [Module S R] (A : ι -> Submodule S R) : SetLike.IsHomogeneousElem A (0 : R)
参数：A : ι -> Submodule S R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
theorem SetLike.homogeneous_zero_submodule [Zero ι] [Semiring S] [AddCommMonoid R] [Module S R]
    (A : ι → Submodule S R) : SetLike.IsHomogeneousElem A (0 : R) :=
  ⟨0, Submodule.zero_mem _⟩
/-
**SetLike.Homogeneous.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SetLike.Homogeneous.smul [CommSemiring S] [Semiring R] [Algebra S R] {A : 
ι -> Submodule S R} {s : S} {r : R} (hr : SetLike.IsHomogeneousElem A r) : SetLi
ke.IsHomogeneousElem A (s • r)
参数：hr : SetLike.IsHomogeneousElem A r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
theorem SetLike.Homogeneous.smul [CommSemiring S] [Semiring R] [Algebra S R] {A : ι → Submodule S R}
    {s : S} {r : R} (hr : SetLike.IsHomogeneousElem A r) : SetLike.IsHomogeneousElem A (s • r) :=
  let ⟨i, hi⟩ := hr
  ⟨i, Submodule.smul_mem _ _ hi⟩

end HomogeneousElement

/-! ### Gradings by canonically linearly ordered additive monoids -/

section LinearOrderedAddCommMonoid

variable [AddCommMonoid ι] [LinearOrder ι] [IsOrderedAddMonoid ι] [DecidableEq ι]

section Semiring

variable [Semiring R] [SetLike σ R] [AddSubmonoidClass σ R]
variable {A : ι → σ} [SetLike.GradedMonoid A]

set_option backward.isDefEq.respectTransparency.types false in
/-
**mul_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_apply_eq_zero {r r' : ⨁ i, A i} {m n : ι} (hr : forall i < m, r i = 0)
 (hr' : forall i < n, r' i = 0) ⦃k : ι⦄ (hk : k < m + n) : (r * r') k = 0
参数：hr : forall i < m, r i = 0；hr' : forall i < n, r' i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
· 使用定理 `DirectSum.coe_mul_apply`：coe_mul_apply [AddMonoid ι] [SetLike.GradedMono
id A] [forall (i : ι) (x : A i), Decidable (x != 0)] (r r' : ⨁ i, A i) (n : ι) :
 ((r * r') n …
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem mul_apply_eq_zero {r r' : ⨁ i, A i} {m n : ι}
    (hr : ∀ i < m, r i = 0) (hr' : ∀ i < n, r' i = 0) ⦃k : ι⦄ (hk : k < m + n) :
    (r * r') k = 0 := by
  classical
  rw [Subtype.ext_iff, ZeroMemClass.coe_zero, coe_mul_apply]
  apply Finset.sum_eq_zero fun x hx ↦ ?_
  obtain (hx | hx) : x.1 < m ∨ x.2 < n := by
    by_contra! ⟨hm, hn⟩
    obtain rfl : x.1 + x.2 = k := by simp_all
    apply lt_irrefl (m + n) <| lt_of_le_of_lt (by gcongr) hk
  all_goals simp [hr, hr', hx]

variable [CanonicallyOrderedAdd ι]

/-- The difference with `DirectSum.listProd_apply_eq_zero` is that the indices at which
the terms of the list are zero is allowed to vary. -/
/-
**listProd_apply_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：listProd_apply_eq_zero' {l : List ((⨁ i, A i) × ι)} (hl : forall xn in l, 
forall k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < (l.map Prod.snd).sum) : (l.map Pr
od.fst).prod n = 0
参数：(⨁ i, A i) × ι；hl : forall xn in l, forall k < xn.2, xn.1 k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `mul_apply_eq_zero`：mul_apply_eq_zero {r r' : ⨁ i, A i} {m n : ι} (hr : f
orall i < m, r i = 0) (hr' : forall i < n, r' i = 0) ⦃k : ι⦄ (hk : k < m + n) : 
(r * r'…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The difference with `DirectSum.listProd_apply_eq_zero` is that the indices at wh
ich
the terms of the list are zero is allowed to vary.
-/
theorem listProd_apply_eq_zero' {l : List ((⨁ i, A i) × ι)}
    (hl : ∀ xn ∈ l, ∀ k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < (l.map Prod.snd).sum) :
    (l.map Prod.fst).prod n = 0 := by
  induction l generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, List.sum_cons,
      List.prod_cons] at hl hn ⊢
    exact mul_apply_eq_zero hl.1 (ih hl.2) hn
/-
**listProd_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：listProd_apply_eq_zero {l : List (⨁ i, A i)} {m : ι} (hl : forall x in l, 
forall k < m, x k = 0) ⦃n : ι⦄ (hn : n < l.length • m) : l.prod n = 0
参数：⨁ i, A i；hl : forall x in l, forall k < m, x k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `mul_apply_eq_zero`：mul_apply_eq_zero {r r' : ⨁ i, A i} {m n : ι} (hr : f
orall i < m, r i = 0) (hr' : forall i < n, r' i = 0) ⦃k : ι⦄ (hk : k < m + n) : 
(r * r'…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem listProd_apply_eq_zero {l : List (⨁ i, A i)} {m : ι}
    (hl : ∀ x ∈ l, ∀ k < m, x k = 0) ⦃n : ι⦄ (hn : n < l.length • m) :
    l.prod n = 0 := by
  -- a proof which uses `DirectSum.listProd_apply_eq_zero'` is actually more work
  induction l generalizing n with
  | nil => simp at hn
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp, List.length_cons, List.prod_cons] at hl hn ⊢
    refine mul_apply_eq_zero hl.1 (ih hl.2) ?_
    simpa [add_smul, add_comm m] using hn

end Semiring

variable [CanonicallyOrderedAdd ι]

section CommSemiring

variable [CommSemiring R] [SetLike σ R] [AddSubmonoidClass σ R]
variable {A : ι → σ} [SetLike.GradedMonoid A]

/-- The difference with `DirectSum.multisetProd_apply_eq_zero` is that the indices at which
the terms of the multiset are zero is allowed to vary. -/
/-
**multisetProd_apply_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multisetProd_apply_eq_zero' {s : Multiset ((⨁ i, A i) × ι)} (hs : forall x
n in s, forall k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < (s.map Prod.snd).sum) : (
s.map Prod.fst).prod n = 0
参数：(⨁ i, A i) × ι；hs : forall xn in s, forall k < xn.2, xn.1 k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `listProd_apply_eq_zero'`：listProd_apply_eq_zero' {l : List ((⨁ i, A i) ×
 ι)} (hl : forall xn in l, forall k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < (l.map
 Prod.snd).su…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a

--- 原说明 ---
The difference with `DirectSum.multisetProd_apply_eq_zero` is that the indices a
t which
the terms of the multiset are zero is allowed to vary.
-/
theorem multisetProd_apply_eq_zero' {s : Multiset ((⨁ i, A i) × ι)}
    (hs : ∀ xn ∈ s, ∀ k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < (s.map Prod.snd).sum) :
    (s.map Prod.fst).prod n = 0 := by
  have := listProd_apply_eq_zero' (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]
/-
**multisetProd_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multisetProd_apply_eq_zero {s : Multiset (⨁ i, A i)} {m : ι} (hs : forall 
x in s, forall k < m, x k = 0) ⦃n : ι⦄ (hn : n < s.card • m) : s.prod n = 0
参数：⨁ i, A i；hs : forall x in s, forall k < m, x k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `listProd_apply_eq_zero`：listProd_apply_eq_zero {l : List (⨁ i, A i)} {m 
: ι} (hl : forall x in l, forall k < m, x k = 0) ⦃n : ι⦄ (hn : n < l.length • m)
 : l.prod n …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.length_toList`：length_toList (s : Multiset α) : s.toList.length
 = card s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
-/
theorem multisetProd_apply_eq_zero {s : Multiset (⨁ i, A i)} {m : ι}
    (hs : ∀ x ∈ s, ∀ k < m, x k = 0) ⦃n : ι⦄ (hn : n < s.card • m) :
    s.prod n = 0 := by
  have := listProd_apply_eq_zero (l := s.toList) (by simpa using hs)
    (by simpa [← Multiset.sum_coe, ← Multiset.map_coe])
  simpa [← Multiset.prod_coe, ← Multiset.map_coe]

/-- The difference with `DirectSum.finsetProd_apply_eq_zero` is that the indices at which
the terms of the multiset are zero is allowed to vary. -/
/-
**finsetProd_apply_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsetProd_apply_eq_zero' {s : Finset ((⨁ i, A i) × ι)} (hs : forall xn in
 s, forall k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < ∑ xn in s, xn.2) : (∏ xn in s
, xn.1) n = 0
参数：(⨁ i, A i) × ι；hs : forall xn in s, forall k < xn.2, xn.1 k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.prod_map_toList`：prod_map_toList (s : Finset ι) (f : ι -> M) : (s
.toList.map f).prod = s.prod f
· 使用定理 `listProd_apply_eq_zero'`：listProd_apply_eq_zero' {l : List ((⨁ i, A i) ×
 ι)} (hl : forall xn in l, forall k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < (l.map
 Prod.snd).su…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_map_toList`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] (s : Finset ι) (f : ι → M), (List.map f s.toList).sum = s.sum f

--- 原说明 ---
The difference with `DirectSum.finsetProd_apply_eq_zero` is that the indices at 
which
the terms of the multiset are zero is allowed to vary.
-/
theorem finsetProd_apply_eq_zero' {s : Finset ((⨁ i, A i) × ι)}
    (hs : ∀ xn ∈ s, ∀ k < xn.2, xn.1 k = 0) ⦃n : ι⦄ (hn : n < ∑ xn ∈ s, xn.2) :
    (∏ xn ∈ s, xn.1) n = 0 := by
  simpa using listProd_apply_eq_zero' (l := s.toList) (by simpa using hs) (by simpa)
/-
**finsetProd_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finsetProd_apply_eq_zero {s : Finset (⨁ i, A i)} {m : ι} (hs : forall x in
 s, forall k < m, x k = 0) ⦃n : ι⦄ (hn : n < s.card • m) : (∏ x in s, x) n = 0
参数：⨁ i, A i；hs : forall x in s, forall k < m, x k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finset.prod_toList`：prod_toList {M : Type*} [CommMonoid M] (s : Finset M
) : s.toList.prod = ∏ x in s, x
· 使用定理 `listProd_apply_eq_zero`：listProd_apply_eq_zero {l : List (⨁ i, A i)} {m 
: ι} (hl : forall x in l, forall k < m, x k = 0) ⦃n : ι⦄ (hn : n < l.length • m)
 : l.prod n …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.length_toList`：length_toList (s : Finset α) : s.toList.length = #
s
-/
theorem finsetProd_apply_eq_zero {s : Finset (⨁ i, A i)} {m : ι}
    (hs : ∀ x ∈ s, ∀ k < m, x k = 0) ⦃n : ι⦄ (hn : n < s.card • m) :
    (∏ x ∈ s, x) n = 0 := by
  simpa using listProd_apply_eq_zero (l := s.toList) (by simpa using hs) (by simpa)

end CommSemiring

end LinearOrderedAddCommMonoid

