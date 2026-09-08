/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.Tactic.SuppressCompilation

/-!
# Symmetric tensor power of a semimodule over a commutative semiring

We define the `ι`-indexed symmetric tensor power of `M` as the `PiTensorProduct` quotiented by
the relation that the `tprod` of `ι` elements is equal to the `tprod` of the same elements permuted
by a permutation of `ι`. We denote this space by `Sym[R] ι M`, and the canonical multilinear map
from `ι → M` to `Sym[R] ι M` by `⨂ₛ[R] i, f i`. We also reserve the notation `Sym[R]^n M` for the
`n`th symmetric tensor power of `M`, which is the symmetric tensor power indexed by `Fin n`.

## Main definitions:

* `SymmetricPower.module`: the symmetric tensor power is a module over `R`.

## TODO:

* Grading: show that there is a map `Sym[R]^i M × Sym[R]^j M → Sym[R]^(i + j) M` that is
  associative and commutative, and that `n ↦ Sym[R]^n M` is a graded (semi)ring and algebra.
* Universal property: linear maps from `Sym[R]^n M` to `N` correspond to symmetric multilinear
  maps `M ^ n` to `N`.
* Relate to homogeneous (multivariate) polynomials of degree `n`.

-/

@[expose] public section

suppress_compilation

universe u v

open TensorProduct Equiv

variable (R ι : Type u) [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M] (s : ι → M)

/-- The relation on the `ι`-indexed tensor power of `M` where two tensors are equal
if they are related by a permutation of `ι`. -/
/-
**SymmetricPower.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `SymmetricPower`。
形式化陈述：(R ι : Type u) →   [inst : CommSemiring R] →     (M : Type v) →       [ins
t_1 : AddCommMonoid M] →         [inst_2 : _root_.Module R M] → (PiTensorProduct
 R fun x => M) → (PiTensorProduct R fun x => M) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation on the `ι`-indexed tensor power of `M` where two tensors are equal
if they are related by a permutation of `ι`.
-/
inductive SymmetricPower.Rel : (⨂[R] _, M) → (⨂[R] _, M) → Prop
  | perm : (e : Perm ι) → (f : ι → M) → Rel (⨂ₜ[R] i, f i) (⨂ₜ[R] i, f (e i))

/-- The `ι`-indexed symmetric tensor power of a semimodule `M` over a commutative semiring `R`
is the quotient of the `ι`-indexed tensor power of `M` by the relation that two tensors are equal
if they are related by a permutation of `ι`. -/
/-
**SymmetricPower** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SymmetricPower : Type max u v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ι`-indexed symmetric tensor power of a semimodule `M` over a commutative se
miring `R`
is the quotient of the `ι`-indexed tensor power of `M` by the relation that two 
tensors are equal
if they are related by a permutation of `ι`.
-/
def SymmetricPower : Type max u v :=
  (addConGen (SymmetricPower.Rel R ι M)).Quotient
deriving AddCommMonoid

@[inherit_doc]
scoped[TensorProduct] notation:max "Sym[" R "] " ι:arg M:arg => SymmetricPower R ι M

/-- The `n`th symmetric tensor power of a semimodule `M` over a commutative semiring `R` -/
scoped[TensorProduct] notation:max "Sym[" R "]^" n:arg M:arg => Sym[R] (Fin n) M

namespace SymmetricPower

/-
**SymmetricPower.** 是 Mathlib 中的一个实例，位于命名空间 `SymmetricPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    AddCommGroup (Sym[R] ι M) :=
  inferInstanceAs <| AddCommGroup (AddCon.Quotient _)

variable {R ι M} in
/-
**SymmetricPower.smul** 是 Mathlib 中的一个引理，位于命名空间 `SymmetricPower`。
形式化陈述：smul (r : R) (x y : ⨂[R] _, M) (h : addConGen (Rel R ι M) x y) : addConGen
 (Rel R ι M) (r • x) (r • y)
参数：r : R；x y : ⨂[R] _, M；h : addConGen (Rel R ι M) x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForallOfFastIsEmpty`：∀ {α : Sort u} [inst 
: Meta.FastIsEmpty α] {β : α → Sort v}, Meta.FastSubsingleton ((x : α) → β x)
· 使用定理 `AddCon.refl`：∀ {M : Type u_1} [inst : Add M] (c : AddCon M) (x : M), c x
 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MultilinearMap.map_update_smul`：∀ {R : Type uR} {ι : Type uι} {M₁ : ι → 
Type v₁} {M₂ : Type v₂} [inst : Semiring R]   [inst_1 : (i : ι) → AddCommMonoid 
(M₁ i)] [inst_2 : Ad…
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.update_apply_equiv_apply`：update_apply_equiv_apply [DecidableEq
 α'] [DecidableEq α] (f : α -> β) (g : α' ≃ α) (a : α) (v : β) (a' : α') : updat
e f a v (g a') = update…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddCon.symm`：∀ {M : Type u_1} [inst : Add M] (c : AddCon M) {x y : M}, c
 x y → c y x
· 使用定理 `AddCon.trans`：∀ {M : Type u_1} [inst : Add M] (c : AddCon M) {x y z : M}
, c x y → c y z → c x z
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `AddCon.add`：∀ {M : Type u_1} [inst : Add M] (c : AddCon M) {w x y z : M}
, c w x → c y z → c (w + y) (x + z)
-/
lemma smul (r : R) (x y : ⨂[R] _, M) (h : addConGen (Rel R ι M) x y) :
    addConGen (Rel R ι M) (r • x) (r • y) := by
  induction h with
  | of x y h => cases h with
    | perm e f =>
      apply isEmpty_or_nonempty ι |>.elim <;> intro h
      · convert! addConGen (Rel R ι M) |>.refl _
      · let i := Nonempty.some h
        classical
        convert!
          AddConGen.Rel.of _ _ <|
            SymmetricPower.Rel.perm (R := R) (ι := ι) e <| Function.update f i (r • f i)
        · rw [MultilinearMap.map_update_smul, Function.update_eq_self]
        · simp_rw [Function.update_apply_equiv_apply, MultilinearMap.map_update_smul,
              ← Function.update_comp_equiv, Function.update_eq_self]; rfl
  | refl => exact AddCon.refl _ _
  | symm => apply AddCon.symm; assumption
  | trans => apply AddCon.trans <;> assumption
  | add => rw [smul_add, smul_add]; apply AddCon.add <;> assumption

variable {R} in
/-- Scalar multiplication by `r : R`. Use `•` instead. -/
/-
**SymmetricPower.smul'** 是 Mathlib 中的一个定义，位于命名空间 `SymmetricPower`。
形式化陈述：smul' (r : R) : Sym[R] ι M ->+ Sym[R] ι M
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Scalar multiplication by `r : R`. Use `•` instead.
-/
def smul' (r : R) : Sym[R] ι M →+ Sym[R] ι M :=
  AddCon.lift _ (AddMonoidHom.comp (AddCon.mk' _) {
      toFun := (r • ·)
      map_zero' := smul_zero r
      map_add' := smul_add r })
    (fun x y h ↦ Quotient.sound (smul r x y h))
/-
**SymmetricPower.module** 是 Mathlib 中的一个实例，位于命名空间 `SymmetricPower`。
形式化陈述：module : Module R (Sym[R] ι M) where smul r x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module : Module R (Sym[R] ι M) where
  smul r x := smul' ι M r x
  one_smul x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| one_smul R x
  mul_smul r s x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| mul_smul r s x
  smul_zero r := congr_arg _ <| smul_zero r
  smul_add r x y := AddCon.induction_on₂ x y <| fun x y ↦ congr_arg _ <| smul_add r x y
  add_smul r s x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| add_smul r s x
  zero_smul x := AddCon.induction_on x <| fun x ↦ congr_arg _ <| zero_smul R x

/-- The canonical map from the `ι`-indexed tensor power to the symmetric tensor power. -/
/-
**SymmetricPower.mk** 是 Mathlib 中的一个定义，位于命名空间 `SymmetricPower`。
形式化陈述：mk : (⨂[R] (_ : ι), M) ->ₗ[R] Sym[R] ι M where map_smul' _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from the `ι`-indexed tensor power to the symmetric tensor powe
r.
-/
def mk : (⨂[R] (_ : ι), M) →ₗ[R] Sym[R] ι M where
  map_smul' _ _ := rfl
  __ := AddCon.mk' _

variable {M ι} in
/-- The multilinear map that takes `ι`-indexed elements of `M` and
returns their symmetric tensor power. Denoted `⨂ₛ[R] i, f i`. -/
/-
**SymmetricPower.tprod** 是 Mathlib 中的一个定义，位于命名空间 `SymmetricPower`。
形式化陈述：tprod : MultilinearMap R (fun _ : ι => M) Sym[R] ι M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multilinear map that takes `ι`-indexed elements of `M` and
returns their symmetric tensor power. Denoted `⨂ₛ[R] i, f i`.
-/
def tprod : MultilinearMap R (fun _ : ι ↦ M) Sym[R] ι M :=
  (mk R ι M).compMultilinearMap (PiTensorProduct.tprod R)

unsuppress_compilation in
@[inherit_doc tprod]
notation3:100 "⨂ₛ["R"] "(...)", "r:(scoped f => tprod R f) => r

variable {R ι M} in
/-
**SymmetricPower.tprod_equiv** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricPower`。
形式化陈述：∀ {R ι : Type u} [inst : CommSemiring R] {M : Type v} [inst_1 : AddCommMon
oid M] [inst_2 : _root_.Module R M]   (e : Equiv.Perm ι) (f : ι → M), (⨂ₛ[R] (i 
: ι), f (e i)) = ⨂ₛ[R] (i : ι), f i
参数：e : Equiv.Perm ι；f : ι → M；⨂ₛ[R] (i : ι), f (e i)；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[simp] lemma tprod_equiv (e : Perm ι) (f : ι → M) :
    (⨂ₛ[R] i, f (e i)) = ⨂ₛ[R] i, f i :=
  Eq.symm <| Quot.sound <| AddConGen.Rel.of _ _ <| Rel.perm e f

variable {R M n} in
/-
**SymmetricPower.domDomCongr_tprod** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricPower`。
形式化陈述：∀ {R : Type u} (ι : Type u) [inst : CommSemiring R] {M : Type v} [inst_1 :
 AddCommMonoid M] [inst_2 : _root_.Module R M]   (e : Equiv.Perm ι), Multilinear
Map.domDomCongr e (SymmetricPower.tprod R) = SymmetricPower.tprod R
参数：ι : Type u；e : Equiv.Perm ι；SymmetricPower.tprod R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.ext`：ext {f f' : MultilinearMap R M₁ M₂} (H : forall x, f
 x = f' x) : f = f'
· 使用定理 `SymmetricPower.tprod_equiv`：∀ {R ι : Type u} [inst : CommSemiring R] {M 
: Type v} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (e : Equiv.P
erm ι) (f : ι → …
-/
@[simp] lemma domDomCongr_tprod (e : Perm ι) :
    (tprod R (ι := ι) (M := M)).domDomCongr e = tprod R :=
  MultilinearMap.ext <| tprod_equiv e
/-
**SymmetricPower.range_mk** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricPower`。
形式化陈述：range_mk : LinearMap.range (mk R ι M) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.range_eq_top_of_surjective`：range_eq_top_of_surjective [RingHo
mSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) : range f = ⊤
· 使用定理 `AddCon.mk'_surjective`：∀ {M : Type u_1} [inst : AddZeroClass M] {c : Add
Con M}, Function.Surjective ⇑c.mk'
-/
theorem range_mk : LinearMap.range (mk R ι M) = ⊤ :=
  LinearMap.range_eq_top_of_surjective _ AddCon.mk'_surjective

/-- The pure tensors (i.e. the elements of the image of `SymmetricPower.tprod`) span the symmetric
tensor power. -/
/-
**SymmetricPower.span_tprod_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricPower`。
形式化陈述：span_tprod_eq_top : Submodule.span R (Set.range (tprod R (ι
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SymmetricPower.tprod.eq_1`：∀ (R : Type u) {ι : Type u} [inst : CommSemir
ing R] {M : Type v} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M],  
 SymmetricPower…
· 使用定理 `LinearMap.coe_compMultilinearMap`：coe_compMultilinearMap (g : M₂ ->ₗ[R] 
M₃) (f : MultilinearMap R M₁ M₂) : ⇑(g.compMultilinearMap f) = g ∘ f
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `PiTensorProduct.span_tprod_eq_top`：span_tprod_eq_top : Submodule.span R 
(Set.range (tprod R)) = (⊤ : Submodule R (⨂[R] i, s i))
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `SymmetricPower.range_mk`：range_mk : LinearMap.range (mk R ι M) = ⊤

--- 原说明 ---
The pure tensors (i.e. the elements of the image of `SymmetricPower.tprod`) span
 the symmetric
tensor power.
-/
theorem span_tprod_eq_top : Submodule.span R (Set.range (tprod R (ι := ι) (M := M))) = ⊤ := by
  rw [tprod, LinearMap.coe_compMultilinearMap, Set.range_comp, Submodule.span_image,
    PiTensorProduct.span_tprod_eq_top, Submodule.map_top, range_mk]

end SymmetricPower

