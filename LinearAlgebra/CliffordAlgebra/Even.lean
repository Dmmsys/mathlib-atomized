/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Fold
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading

/-!
# The universal property of the even subalgebra

## Main definitions

* `CliffordAlgebra.even Q`: The even subalgebra of `CliffordAlgebra Q`.
* `CliffordAlgebra.EvenHom`: The type of bilinear maps that satisfy the universal property of the
  even subalgebra
* `CliffordAlgebra.even.lift`: The universal property of the even subalgebra, which states
  that every bilinear map `f` with `f v v = Q v` and `f u v * f v w = Q v • f u w` is in unique
  correspondence with an algebra morphism from `CliffordAlgebra.even Q`.

## Implementation notes

The approach here is outlined in "Computing with the universal properties of the Clifford algebra
and the even subalgebra" (to appear).

The broad summary is that we have two tricks available to us for implementing complex recursors on
top of `CliffordAlgebra.lift`: the first is to use morphisms as the output type, such as
`A = Module.End R N` which is how we obtained `CliffordAlgebra.foldr`; and the second is to use
`N = (N', S)` where `N'` is the value we wish to compute, and `S` is some auxiliary state passed
between one recursor invocation and the next.
For the universal property of the even subalgebra, we apply a variant of the first trick again by
choosing `S` to itself be a submodule of morphisms.
-/

@[expose] public section


namespace CliffordAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

-- put this after `Q` since we want to talk about morphisms from `CliffordAlgebra Q` to `A` and
-- that order is more natural
variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

open scoped DirectSum

variable (Q)

/-- The even submodule `CliffordAlgebra.evenOdd Q 0` is also a subalgebra. -/
/-
**CliffordAlgebra.even** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：even : Subalgebra R (CliffordAlgebra Q)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The even submodule `CliffordAlgebra.evenOdd Q 0` is also a subalgebra.
-/
def even : Subalgebra R (CliffordAlgebra Q) :=
  (evenOdd Q 0).toSubalgebra (SetLike.one_mem_graded _) fun _x _y hx hy =>
    add_zero (0 : ZMod 2) ▸ SetLike.mul_mem_graded hx hy

@[simp]
/-
**CliffordAlgebra.even_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：even_toSubmodule : Subalgebra.toSubmodule (even Q) = evenOdd Q 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem even_toSubmodule : Subalgebra.toSubmodule (even Q) = evenOdd Q 0 :=
  rfl

variable (A)

/-- The type of bilinear maps which are accepted by `CliffordAlgebra.even.lift`. -/
@[ext]
/-
**CliffordAlgebra.EvenHom** 是 Mathlib 中的一个归纳类型，位于命名空间 `CliffordAlgebra`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommRing R] →       [inst_
1 : AddCommGroup M] →         [inst_2 : _root_.Module R M] →           Quadratic
Form R M → (A : Type u_3) → [inst_3 : Ring A] → [Algebra R A] → Type (max u_2 u_
3)
参数：A : Type u_3；max u_2 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of bilinear maps which are accepted by `CliffordAlgebra.even.lift`.
-/
structure EvenHom where
  bilin : M →ₗ[R] M →ₗ[R] A
  contract (m : M) : bilin m m = algebraMap R A (Q m)
  contract_mid (m₁ m₂ m₃ : M) : bilin m₁ m₂ * bilin m₂ m₃ = Q m₂ • bilin m₁ m₃

variable {A Q}

/-- Compose an `EvenHom` with an `AlgHom` on the output. -/
@[simps]
/-
**CliffordAlgebra.EvenHom.compr** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose an `EvenHom` with an `AlgHom` on the output.
-/
def EvenHom.compr₂ (g : EvenHom Q A) (f : A →ₐ[R] B) : EvenHom Q B where
  bilin := g.bilin.compr₂ f.toLinearMap
  contract _m := (f.congr_arg <| g.contract _).trans <| f.commutes _
  contract_mid _m₁ _m₂ _m₃ :=
    (map_mul f _ _).symm.trans <| (f.congr_arg <| g.contract_mid _ _ _).trans <| map_smul f _ _

variable (Q)

/-- The embedding of pairs of vectors into the even subalgebra, as a bilinear map. -/
nonrec def even.ι : EvenHom Q (even Q) where
  bilin :=
    LinearMap.mk₂ R (fun m₁ m₂ => ⟨ι Q m₁ * ι Q m₂, ι_mul_ι_mem_evenOdd_zero Q _ _⟩)
      (fun _ _ _ => by simp only [map_add, add_mul]; rfl)
      (fun _ _ _ => by simp only [map_smul, smul_mul_assoc]; rfl)
      (fun _ _ _ => by simp only [map_add, mul_add]; rfl) fun _ _ _ => by
      simp only [map_smul, mul_smul_comm]; rfl
  contract m := Subtype.ext <| ι_sq_scalar Q m
  contract_mid m₁ m₂ m₃ :=
    Subtype.ext <|
      calc
        ι Q m₁ * ι Q m₂ * (ι Q m₂ * ι Q m₃) = ι Q m₁ * (ι Q m₂ * ι Q m₂ * ι Q m₃) := by
          simp only [mul_assoc]
        _ = Q m₂ • (ι Q m₁ * ι Q m₃) := by rw [Algebra.smul_def, ι_sq_scalar, Algebra.left_comm]

/-
**CliffordAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (EvenHom Q (even Q)) :=
  ⟨even.ι Q⟩

variable (f : EvenHom Q A)

/-- Two algebra morphisms from the even subalgebra are equal if they agree on pairs of generators.

See note [partially-applied ext lemmas]. -/
@[ext high]
/-
**CliffordAlgebra.even.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra.eve
n`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   (Q : QuadraticForm R M) {A : Type u_3} [inst_
3 : Ring A] [inst_4 : Algebra R A]   ⦃f g : ↥(CliffordAlgebra.even Q) →ₐ[R] A⦄, 
  (CliffordAlgebra.even.ι Q).compr₂ f = (CliffordAlgebra.even.ι Q).compr₂ g → f 
= g
参数：Q : QuadraticForm R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `CliffordAlgebra.even_induction`：even_induction {motive : forall x, x in 
evenOdd Q 0 -> Prop} (algebraMap : forall r : R, motive (algebraMap _ _ r) (SetL
ike.algebraMap_mem_g…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SetLike.algebraMap_mem_graded`：SetLike.algebraMap_mem_graded [Zero ι] [C
ommSemiring S] [Semiring R] [Algebra S R] (A : ι -> Submodule S R) [SetLike.Grad
edOne A] (s : S) : …
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `CliffordAlgebra.evenOdd.gradedMonoid`：∀ {R : Type u_1} {M : Type u_2} [i
nst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q : 
QuadraticForm R M), SetLik…
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.EvenHom.ext_iff`：∀ {R : Type u_1} {M : Type u_2} {inst :
 CommRing R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   {Q : Quadr
aticForm R M} {A : Ty…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…

--- 原说明 ---
Two algebra morphisms from the even subalgebra are equal if they agree on pairs 
of generators.

See note [partially-applied ext lemmas].
-/
theorem even.algHom_ext ⦃f g : even Q →ₐ[R] A⦄ (h : (even.ι Q).compr₂ f = (even.ι Q).compr₂ g) :
    f = g := by
  rw [EvenHom.ext_iff] at h
  ext ⟨x, hx⟩
  induction x, hx using even_induction with
  | algebraMap r =>
    exact (f.commutes r).trans (g.commutes r).symm
  | add x y hx hy ihx ihy =>
    have := congr_arg₂ (· + ·) ihx ihy
    exact (map_add f _ _).trans (this.trans <| (map_add g _ _).symm)
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    have := congr_arg₂ (· * ·) (LinearMap.congr_fun (LinearMap.congr_fun h m₁) m₂) ih
    exact (map_mul f _ _).trans (this.trans <| (map_mul g _ _).symm)

variable {Q}

namespace even.lift

set_option backward.privateInPublic true in
/-- An auxiliary submodule used to store the half-applied values of `f`.
This is the span of elements `f'` such that `∃ x m₂, ∀ m₁, f' m₁ = f m₁ m₂ * x`. -/
/-
**CliffordAlgebra.even.lift.S** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra.even.li
ft`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary submodule used to store the half-applied values of `f`.
This is the span of elements `f'` such that `∃ x m₂, ∀ m₁, f' m₁ = f m₁ m₂ * x`.
-/
private def S : Submodule R (M →ₗ[R] A) :=
  Submodule.span R
    {f' | ∃ x m₂, f' = LinearMap.lcomp R _ (f.bilin.flip m₂) (LinearMap.mulRight R x)}

set_option backward.privateInPublic true in
/-- An auxiliary bilinear map that is later passed into `CliffordAlgebra.foldr`. Our desired result
is stored in the `A` part of the accumulator, while auxiliary recursion state is stored in the `S f`
part. -/
/-
**CliffordAlgebra.even.lift.fFold** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra.eve
n.lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary bilinear map that is later passed into `CliffordAlgebra.foldr`. Our
 desired result
is stored in the `A` part of the accumulator, while auxiliary recursion state is
 stored in the `S f`
part.
-/
private def fFold : M →ₗ[R] A × S f →ₗ[R] A × S f :=
  LinearMap.mk₂ R
    (fun m acc =>
      /- We could write this `snd` term in a point-free style as follows, but it wouldn't help as we
        don't have any prod or subtype combinators to deal with n-linear maps of this degree.
        ```lean
        (LinearMap.lcomp R _ (Algebra.lmul R A).to_linear_map.flip).comp <|
          (LinearMap.llcomp R M A A).flip.comp f.flip : M →ₗ[R] A →ₗ[R] M →ₗ[R] A)
        ```
        -/
      (acc.2.val m,
        ⟨(LinearMap.mulRight R acc.1).comp (f.bilin.flip m), Submodule.subset_span <| ⟨_, _, rfl⟩⟩))
    (fun m₁ m₂ a =>
      Prod.ext (map_add _ m₁ m₂)
        (Subtype.ext <|
          LinearMap.ext fun m₃ =>
            show f.bilin m₃ (m₁ + m₂) * a.1 = f.bilin m₃ m₁ * a.1 + f.bilin m₃ m₂ * a.1 by
              rw [map_add, add_mul]))
    (fun c m a =>
      Prod.ext (map_smul _ c m)
        (Subtype.ext <|
          LinearMap.ext fun m₃ =>
            show f.bilin m₃ (c • m) * a.1 = c • (f.bilin m₃ m * a.1) by
              rw [map_smul, smul_mul_assoc]))
    (fun _ _ _ => Prod.ext rfl (Subtype.ext <| LinearMap.ext fun _ => mul_add _ _ _))
    fun _ _ _ => Prod.ext rfl (Subtype.ext <| LinearMap.ext fun _ => mul_smul_comm _ _ _)

@[simp]
/-
**CliffordAlgebra.even.lift.fst_fFold_fFold** 是 Mathlib 中的一个定理，位于命名空间 `CliffordA
lgebra.even.lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem fst_fFold_fFold (m₁ m₂ : M) (x : A × S f) :
    (fFold f m₁ (fFold f m₂ x)).fst = f.bilin m₁ m₂ * x.fst :=
  rfl

@[simp]
/-
**CliffordAlgebra.even.lift.snd_fFold_fFold** 是 Mathlib 中的一个定理，位于命名空间 `CliffordA
lgebra.even.lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem snd_fFold_fFold (m₁ m₂ m₃ : M) (x : A × S f) :
    ((fFold f m₁ (fFold f m₂ x)).snd : M →ₗ[R] A) m₃ = f.bilin m₃ m₁ * (x.snd : M →ₗ[R] A) m₂ :=
  rfl

set_option backward.privateInPublic true in
/-
**CliffordAlgebra.even.lift.fFold_fFold** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra.even.lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem fFold_fFold (m : M) (x : A × S f) : fFold f m (fFold f m x) = Q m • x := by
  obtain ⟨a, ⟨g, hg⟩⟩ := x
  ext : 2
  · change f.bilin m m * a = Q m • a
    rw [Algebra.smul_def, f.contract]
  · ext m₁
    change f.bilin _ _ * g m = Q m • g m₁
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨b, m₃, rfl⟩
      change f.bilin _ _ * (f.bilin _ _ * b) = Q m • (f.bilin _ _ * b)
      rw [← smul_mul_assoc, ← mul_assoc, f.contract_mid]
    · simp
    · rintro x y _hx _hy ihx ihy
      rw [LinearMap.add_apply, LinearMap.add_apply, mul_add, smul_add, ihx, ihy]
    · rintro x hx _c ihx
      rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul_comm, ihx, smul_comm]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The final auxiliary construction for `CliffordAlgebra.even.lift`. This map is the forwards
direction of that equivalence, but not in the fully-bundled form. -/
@[simps! -isSimp apply]
/-
**CliffordAlgebra.even.lift.aux** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra.even.
lift`。
形式化陈述：aux (f : EvenHom Q A) : CliffordAlgebra.even Q ->ₗ[R] A
参数：f : EvenHom Q A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.LinearAlgebra.CliffordAlgebra.Even.0.CliffordAlgebra.ev
en.lift.fFold_fFold`：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M} {A : T
y…

--- 原说明 ---
The final auxiliary construction for `CliffordAlgebra.even.lift`. This map is th
e forwards
direction of that equivalence, but not in the fully-bundled form.
-/
def aux (f : EvenHom Q A) : CliffordAlgebra.even Q →ₗ[R] A := by
  refine ?_ ∘ₗ (even Q).val.toLinearMap
  exact LinearMap.fst R _ _ ∘ₗ foldr Q (fFold f) (fFold_fFold f) (1, 0)

@[simp]
/-
**CliffordAlgebra.even.lift.aux_one** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra.e
ven.lift`。
形式化陈述：aux_one : aux f 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.CliffordAlgebra.Even.0.CliffordAlgebra.ev
en.lift.fFold_fFold`：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M} {A : T
y…
· 使用定理 `CliffordAlgebra.foldr_one`：foldr_one (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n :
 N) : foldr Q f hf n 1 = n
-/
theorem aux_one : aux f 1 = 1 :=
  congr_arg Prod.fst (foldr_one _ _ _ _)

@[simp]
/-
**CliffordAlgebra.even.lift.aux_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra.even
.lift`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem aux_ι (m₁ m₂ : M) : aux f ((even.ι Q).bilin m₁ m₂) = f.bilin m₁ m₂ := by
  rw [CliffordAlgebra.even.lift.aux_apply]
  refine (congr_arg Prod.fst (foldr_mul Q (fFold f) _ _ _ _)).trans ?_
  rw [foldr_ι, foldr_ι]
  exact mul_one _

@[simp]
/-
**CliffordAlgebra.even.lift.aux_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAl
gebra.even.lift`。
形式化陈述：aux_algebraMap (r) : aux f (algebraMap R (even Q) r) = algebraMap R A r
参数：r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.LinearAlgebra.CliffordAlgebra.Even.0.CliffordAlgebra.ev
en.lift.fFold_fFold`：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M} {A : T
y…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CliffordAlgebra.foldr_algebraMap`：foldr_algebraMap (f : M ->ₗ[R] N ->ₗ[R
] N) (hf) (n : N) (r : R) : foldr Q f hf n (algebraMap R _ r) = r • n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
theorem aux_algebraMap (r) :
    aux f (algebraMap R (even Q) r) = algebraMap R A r :=
  (congr_arg Prod.fst (foldr_algebraMap _ _ _ _ _)).trans (Algebra.algebraMap_eq_smul_one r).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CliffordAlgebra.even.lift.aux_mul** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra.e
ven.lift`。
形式化陈述：aux_mul (x y : even Q) : aux f (x * y) = aux f x * aux f y
参数：x y : even Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `_private.Mathlib.LinearAlgebra.CliffordAlgebra.Even.0.CliffordAlgebra.ev
en.lift.fFold_fFold`：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : QuadraticForm R M} {A : T
y…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `CliffordAlgebra.foldr_mul`：foldr_mul (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n :
 N) (a b : CliffordAlgebra Q) : foldr Q f hf n (a * b) = foldr Q f hf (foldr Q f
 hf n b) a
· 使用定理 `CliffordAlgebra.even_induction`：even_induction {motive : forall x, x in 
evenOdd Q 0 -> Prop} (algebraMap : forall r : R, motive (algebraMap _ _ r) (SetL
ike.algebraMap_mem_g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.foldr_algebraMap`：foldr_algebraMap (f : M ->ₗ[R] N ->ₗ[R
] N) (hf) (n : N) (r : R) : foldr Q f hf n (algebraMap R _ r) = r • n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CliffordAlgebra.even.lift.aux_algebraMap`：aux_algebraMap (r) : aux f (al
gebraMap R (even Q) r) = algebraMap R A r
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `SetLike.algebraMap_mem_graded`：SetLike.algebraMap_mem_graded [Zero ι] [C
ommSemiring S] [Semiring R] [Algebra S R] (A : ι -> Submodule S R) [SetLike.Grad
edOne A] (s : S) : …
· 使用定理 `SetLike.GradedMonoid.toGradedOne`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `CliffordAlgebra.evenOdd.gradedMonoid`：∀ {R : Type u_1} {M : Type u_2} [i
nst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q : 
QuadraticForm R M), SetLik…
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Prod.fst_add`：∀ {M : Type u_8} {N : Type u_9} [inst : Add M] [inst_1 : A
dd N] (p q : M × N), (p + q).1 = p.1 + q.1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SetLike.mul_mem_graded`：SetLike.mul_mem_graded {S : Type*} [SetLike S R]
 [Mul R] [Add ι] {A : ι -> S} [SetLike.GradedMul A] ⦃i j⦄ {gi gj} (hi : gi in A 
i) (hj : gj …
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero`：ι_mul_ι_mem_evenOdd_zero (m₁ m
₂ : M) : ι Q m₁ * ι Q m₂ in evenOdd Q 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CliffordAlgebra.foldr_ι`：foldr_ι (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) 
(m : M) : foldr Q f hf n (ι Q m) = f m n
· 使用定理 `CliffordAlgebra.even.lift.aux_apply`：∀ {R : Type u_1} {M : Type u_2} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Q
uadraticForm R M} {A : Ty…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem aux_mul (x y : even Q) : aux f (x * y) = aux f x * aux f y := by
  obtain ⟨x, x_property⟩ := x
  cases y
  refine (congr_arg Prod.fst (foldr_mul _ _ _ _ _ _)).trans ?_
  dsimp only
  induction x, x_property using even_induction Q with
  | algebraMap r =>
    generalize_proofs at ⊢
    simpa using! Algebra.smul_def r _
  | add x y hx hy ihx ihy =>
    rw [map_add, Prod.fst_add]
    simp [ihx, ihy, ← add_mul, ← map_add]
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    simp [aux_apply, ih, ← mul_assoc]

end even.lift

open even.lift

variable (Q)

/-- Every algebra morphism from the even subalgebra is in one-to-one correspondence with a
bilinear map that sends duplicate arguments to the quadratic form, and contracts across
multiplication. -/
@[simps! symm_apply_bilin]
/-
**CliffordAlgebra.even.lift** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra.even`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommRing R] →       [inst_
1 : AddCommGroup M] →         [inst_2 : _root_.Module R M] →           (Q : Quad
raticForm R M) →             {A : Type u_3} →               [inst_3 : Ring A] → 
                [inst_4 : Algebra R A] → CliffordAlgebra.EvenHom Q A ≃ (↥(Cliffo
rdAlgebra.even Q) →ₐ[R] A)
参数：Q : QuadraticForm R M；↥(CliffordAlgebra.even Q) →ₐ[R] A。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.even.lift.aux_one`：aux_one : aux f 1 = 1
· 使用定理 `CliffordAlgebra.even.lift.aux_mul`：aux_mul (x y : even Q) : aux f (x * y
) = aux f x * aux f y

--- 原说明 ---
Every algebra morphism from the even subalgebra is in one-to-one correspondence 
with a
bilinear map that sends duplicate arguments to the quadratic form, and contracts
 across
multiplication.
-/
def even.lift : EvenHom Q A ≃ (CliffordAlgebra.even Q →ₐ[R] A) where
  toFun f := AlgHom.ofLinearMap (aux f) (aux_one f) (aux_mul f)
  invFun F := (even.ι Q).compr₂ F
  left_inv f := EvenHom.ext <| LinearMap.ext₂ <| even.lift.aux_ι f
  right_inv _ := even.algHom_ext Q <| EvenHom.ext <| LinearMap.ext₂ <| even.lift.aux_ι _

@[simp]
/-
**CliffordAlgebra.even.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem even.lift_ι (f : EvenHom Q A) (m₁ m₂ : M) :
    even.lift Q f ((even.ι Q).bilin m₁ m₂) = f.bilin m₁ m₂ :=
  even.lift.aux_ι _ _ _

end CliffordAlgebra

