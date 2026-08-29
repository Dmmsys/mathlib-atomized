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

variable (R ι : Type u) [CommSemiring R] (M : Type v) [AddCommMonoid M] [Module R M] (s : ι -> M)

/--
Inductive type `SymmetricPower.Rel` / 归纳类型 `SymmetricPower.Rel`

English:
inductive SymmetricPower.Rel
  parameters: : (⨂[R] _, M) -> (⨂[R] _, M) -> Prop
  constructors (1):
    - perm: (e : Perm ι) -> (f : ι -> M) -> Rel (⨂ₜ[R] i, f i) (⨂ₜ[R] i, f (e i))

中文:
归纳类型 SymmetricPower.Rel
  参数: : (⨂[R] _, M) -> (⨂[R] _, M) -> 命题
  构造子 (1 个):
    - perm: (e : Perm ι) -> (f : ι -> M) -> Rel (⨂ₜ[R] i, f i) (⨂ₜ[R] i, f (e i))
-/
inductive SymmetricPower.Rel : (⨂[R] _, M) -> (⨂[R] _, M) -> Prop
  | perm : (e : Perm ι) -> (f : ι -> M) -> Rel (⨂ₜ[R] i, f i) (⨂ₜ[R] i, f (e i))

/--
Definition of `SymmetricPower` / `SymmetricPower` 的定义

English:
definition SymmetricPower
  signature: : Type max u v
  body: (addConGen (SymmetricPower.Rel R ι M)).Quotient
deriving AddCommMonoid

@[inherit_doc]
scoped[TensorProduct] notation:max "Sym[" R "] " ι:arg M:arg => SymmetricPower R ι M

中文:
定义 SymmetricPower
  签名: : Type max u v
  定义体: (addConGen (SymmetricPower.Rel R ι M)).Quotient
deriving AddCommMonoid

@[inherit_doc]
scoped[TensorProduct] notation:max "Sym[" R "] " ι:arg M:arg => SymmetricPower R ι M

Depends on / 依赖: Quotient, SymmetricPower, SymmetricPower.Rel, addConGen
-/
def SymmetricPower : Type max u v :=
  (addConGen (SymmetricPower.Rel R ι M)).Quotient
deriving AddCommMonoid

@[inherit_doc]
scoped[TensorProduct] notation:max "Sym[" R "] " ι:arg M:arg => SymmetricPower R ι M

/-- The `n`th symmetric tensor power of a semimodule `M` over a commutative semiring `R` -/
scoped[TensorProduct] notation:max "Sym[" R "]^" n:arg M:arg => Sym[R] (Fin n) M

namespace SymmetricPower

instance (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    AddCommGroup (Sym[R] ι M) :=
inferInstanceAs AddCommGroup (AddCon.Quotient _)

variable {R ι M} in
/--
lemma `smul` / 引理 `smul`

English:
lemma smul
  given: (r : R) (x y : ⨂[R] _, M) (h : addConGen (Rel R ι M) x y)
  proof: by
  induction h with
  | of x y h => cases h with
    | perm e f =>
.elim <;> intro h apply isEmpty_or_nonempty ι
.refl _ · convert! addConGen (Rel R ι M)
      · let i := Nonempty.some h
        classical
        convert!
AddConGen.Rel.of _ _
SymmetricPower.Rel.perm (R := R) (ι := ι) e Function.up

中文:
引理 smul
  条件: (r : R) (x y : ⨂[R] _, M) (h : addConGen (Rel R ι M) x y)
  证明: by
  induction h with
  | of x y h => cases h with
    | perm e f =>
.elim <;> intro h apply isEmpty_or_nonempty ι
.refl _ · convert! addConGen (Rel R ι M)
      · let i := Nonempty.some h
        classical
        convert!
AddConGen.Rel.of _ _
SymmetricPower.Rel.perm (R := R) (ι := ι) e Function.up

Depends on / 依赖: AddConGen, AddConGen.Rel.of, Function, Function.update, Function.update_apply_equiv_apply, Function.update_comp_equiv, Function.update_eq_self, MultilinearMap, MultilinearMap.map_update_smul, Nonempty, Nonempty.some, SymmetricPower, SymmetricPower.Rel.perm, addConGen, classical, convert, isEmpty_or_nonempty, map_update_smul, simp_rw, update
-/
lemma smul (r : R) (x y : ⨂[R] _, M) (h : addConGen (Rel R ι M) x y) :
    addConGen (Rel R ι M) (r • x) (r • y) := by
  induction h with
  | of x y h => cases h with
    | perm e f =>
.elim <;> intro h apply isEmpty_or_nonempty ι
.refl _ · convert! addConGen (Rel R ι M)
      · let i := Nonempty.some h
        classical
        convert!
AddConGen.Rel.of _ _
SymmetricPower.Rel.perm (R := R) (ι := ι) e Function.update f i (r • f i)
        · rw [MultilinearMap.map_update_smul, Function.update_eq_self]
        · simp_rw [Function.update_apply_equiv_apply, MultilinearMap.map_update_smul,
              ← Function.update_comp_equiv, Function.update_eq_self]; rfl
  | refl => exact AddCon.refl _ _
  | symm => apply AddCon.symm; assumption
  | trans => apply AddCon.trans <;> assumption
  | add => rw [smul_add, smul_add]; apply AddCon.add <;> assumption

variable {R} in
/--
Definition of `smul'` / `smul'` 的定义

English:
definition smul'
  signature: (r : R)
  body: AddCon.lift _ (AddMonoidHom.comp (AddCon.mk' _) {
      toFun := (r • ·)
      map_zero' := smul_zero r
      map_add' := smul_add r })
    (fun x y h => Quotient.sound (smul r x y h))

中文:
定义 smul'
  签名: (r : R)
  定义体: AddCon.lift _ (AddMonoidHom.comp (AddCon.mk' _) {
      toFun := (r • ·)
      map_zero' := smul_zero r
      map_add' := smul_add r })
    (fun x y h => Quotient.sound (smul r x y h))

Depends on / 依赖: AddCon, AddCon.lift, AddCon.mk, AddMonoidHom, AddMonoidHom.comp, Quotient, Quotient.sound, map_add, map_zero, smul_add, smul_zero
-/
def smul' (r : R) : Sym[R] ι M ->+ Sym[R] ι M :=
  AddCon.lift _ (AddMonoidHom.comp (AddCon.mk' _) {
      toFun := (r • ·)
      map_zero' := smul_zero r
      map_add' := smul_add r })
    (fun x y h => Quotient.sound (smul r x y h))

/--
Instance `module` / 实例 `module`

English:
instance module
  signature: : Module R (Sym[R] ι M) where
  body: smul' ι M r x
one_smul x := AddCon.induction_on x fun x => congr_arg _ one_smul R x
mul_smul r s x := AddCon.induction_on x fun x => congr_arg _ mul_smul r s x
smul_zero r := congr_arg _ smul_zero r
smul_add r x y := AddCon.induction_on₂ x y fun x y => congr_arg _ smul_add r x y
add_smul r s x := Ad

中文:
实例 module
  签名: : Module R (Sym[R] ι M) where
  定义体: smul' ι M r x
one_smul x := AddCon.induction_on x fun x => congr_arg _ one_smul R x
mul_smul r s x := AddCon.induction_on x fun x => congr_arg _ mul_smul r s x
smul_zero r := congr_arg _ smul_zero r
smul_add r x y := AddCon.induction_on₂ x y fun x y => congr_arg _ smul_add r x y
add_smul r s x := Ad
-/
instance module : Module R (Sym[R] ι M) where
  smul r x := smul' ι M r x
one_smul x := AddCon.induction_on x fun x => congr_arg _ one_smul R x
mul_smul r s x := AddCon.induction_on x fun x => congr_arg _ mul_smul r s x
smul_zero r := congr_arg _ smul_zero r
smul_add r x y := AddCon.induction_on₂ x y fun x y => congr_arg _ smul_add r x y
add_smul r s x := AddCon.induction_on x fun x => congr_arg _ add_smul r s x
zero_smul x := AddCon.induction_on x fun x => congr_arg _ zero_smul R x

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : (⨂[R] (_ : ι), M) ->ₗ[R] Sym[R] ι M where
  body: rfl
  __ := AddCon.mk' _

中文:
定义 mk
  签名: : (⨂[R] (_ : ι), M) ->ₗ[R] Sym[R] ι M where
  定义体: rfl
  __ := AddCon.mk' _
-/
def mk : (⨂[R] (_ : ι), M) ->ₗ[R] Sym[R] ι M where
  map_smul' _ _ := rfl
  __ := AddCon.mk' _

variable {M ι} in
/--
Definition of `tprod` / `tprod` 的定义

English:
definition tprod
  signature: : MultilinearMap R (fun _ : ι => M) Sym[R] ι M
  body: (mk R ι M).compMultilinearMap (PiTensorProduct.tprod R)

unsuppress_compilation in
@[inherit_doc tprod]
notation3:100 "⨂ₛ["R"] "(...)", "r:(scoped f => tprod R f) => r

中文:
定义 tprod
  签名: : MultilinearMap R (fun _ : ι => M) Sym[R] ι M
  定义体: (mk R ι M).compMultilinearMap (PiTensorProduct.tprod R)

unsuppress_compilation in
@[inherit_doc tprod]
notation3:100 "⨂ₛ["R"] "(...)", "r:(scoped f => tprod R f) => r

Depends on / 依赖: PiTensorProduct, PiTensorProduct.tprod, compMultilinearMap
-/
def tprod : MultilinearMap R (fun _ : ι => M) Sym[R] ι M :=
  (mk R ι M).compMultilinearMap (PiTensorProduct.tprod R)

unsuppress_compilation in
@[inherit_doc tprod]
notation3:100 "⨂ₛ["R"] "(...)", "r:(scoped f => tprod R f) => r

variable {R ι M} in
/--
lemma `tprod_equiv` / 引理 `tprod_equiv`

English:
lemma tprod_equiv
  given: (e : Perm ι) (f : ι -> M)
  proof: Eq.symm Quot.sound AddConGen.Rel.of _ _ Rel.perm e f

中文:
引理 tprod_equiv
  条件: (e : Perm ι) (f : ι -> M)
  证明: Eq.symm Quot.sound AddConGen.Rel.of _ _ Rel.perm e f

Depends on / 依赖: SignedMeasure, haveLebesgueDecomposition_of_sigmaFinite
-/
@[simp] lemma tprod_equiv (e : Perm ι) (f : ι -> M) :
    (⨂ₛ[R] i, f (e i)) = ⨂ₛ[R] i, f i :=
Eq.symm Quot.sound AddConGen.Rel.of _ _ Rel.perm e f

variable {R M n} in
/--
lemma `domDomCongr_tprod` / 引理 `domDomCongr_tprod`

English:
lemma domDomCongr_tprod
  given: (e : Perm ι)
  proof: MultilinearMap.ext tprod_equiv e

中文:
引理 domDomCongr_tprod
  条件: (e : Perm ι)
  证明: MultilinearMap.ext tprod_equiv e
-/
@[simp] lemma domDomCongr_tprod (e : Perm ι) :
    (tprod R (ι := ι) (M := M)).domDomCongr e = tprod R :=
MultilinearMap.ext tprod_equiv e

/--
theorem `range_mk` / 定理 `range_mk`

English:
theorem range_mk
  statement: LinearMap.range (mk R ι M) = ⊤
  proof: LinearMap.range_eq_top_of_surjective _ AddCon.mk'_surjective

中文:
定理 range_mk
  结论: LinearMap.range (mk R ι M) = ⊤
  证明: LinearMap.range_eq_top_of_surjective _ AddCon.mk'_surjective

Depends on / 依赖: AddCon, AddCon.mk, LinearMap, LinearMap.range_eq_top_of_surjective, _surjective, range_eq_top_of_surjective
-/
theorem range_mk : LinearMap.range (mk R ι M) = ⊤ :=
  LinearMap.range_eq_top_of_surjective _ AddCon.mk'_surjective

/--
theorem `span_tprod_eq_top` / 定理 `span_tprod_eq_top`

English:
theorem span_tprod_eq_top
  statement: Submodule.span R (Set.range (tprod R (ι := ι) (M := M))) = ⊤
  proof: by
  rw [tprod]; rw [LinearMap.coe_compMultilinearMap]; rw [Set.range_comp]; rw [Submodule.span_image]; rw [PiTensorProduct.span_tprod_eq_top]; rw [Submodule.map_top]; rw [range_mk]

中文:
定理 span_tprod_eq_top
  结论: Submodule.span R (Set.range (tprod R (ι := ι) (M := M))) = ⊤
  证明: by
  rw [tprod]; rw [LinearMap.coe_compMultilinearMap]; rw [Set.range_comp]; rw [Submodule.span_image]; rw [PiTensorProduct.span_tprod_eq_top]; rw [Submodule.map_top]; rw [range_mk]

Depends on / 依赖: LinearMap, LinearMap.coe_compMultilinearMap, PiTensorProduct, PiTensorProduct.span_tprod_eq_top, Set.range_comp, Submodule, Submodule.map_top, Submodule.span_image, coe_compMultilinearMap, map_top, range_comp, range_mk, span_image, span_tprod_eq_top
-/
theorem span_tprod_eq_top : Submodule.span R (Set.range (tprod R (ι := ι) (M := M))) = ⊤ := by
  rw [tprod]; rw [LinearMap.coe_compMultilinearMap]; rw [Set.range_comp]; rw [Submodule.span_image]; rw [PiTensorProduct.span_tprod_eq_top]; rw [Submodule.map_top]; rw [range_mk]

end SymmetricPower
