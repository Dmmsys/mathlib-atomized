/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Recursive computation rules for the Clifford algebra

This file provides API for a special case `CliffordAlgebra.foldr` of the universal property
`CliffordAlgebra.lift` with `A = Module.End R N` for some arbitrary module `N`. This specialization
resembles the `list.foldr` operation, allowing a bilinear map to be "folded" along the generators.

For convenience, this file also provides `CliffordAlgebra.foldl`, implemented via
`CliffordAlgebra.reverse`

## Main definitions

* `CliffordAlgebra.foldr`: a computation rule for building linear maps out of the clifford
  algebra starting on the right, analogous to using `list.foldr` on the generators.
* `CliffordAlgebra.foldl`: a computation rule for building linear maps out of the clifford
  algebra starting on the left, analogous to using `list.foldl` on the generators.

## Main statements

* `CliffordAlgebra.right_induction`: an induction rule that adds generators from the right.
* `CliffordAlgebra.left_induction`: an induction rule that adds generators from the left.
-/

@[expose] public section


universe u1 u2 u3

variable {R M N : Type*}
variable [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]
variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

section Foldr

/--
Definition of `foldr` / `foldr` 的定义

English:
definition foldr
  signature: (f : M ->ₗ[R] N ->ₗ[R] N) (hf : forall m x, f m (f m x) = Q m • x)
  body: (CliffordAlgebra.lift Q ⟨f, fun v => LinearMap.ext <| hf v⟩).toLinearMap.flip

@[simp]

中文:
定义 foldr
  签名: (f : M ->ₗ[R] N ->ₗ[R] N) (hf : 对任意 m x, f m (f m x) = Q m • x)
  定义体: (CliffordAlgebra.lift Q ⟨f, fun v => LinearMap.ext <| hf v⟩).toLinearMap.flip

@[simp]

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.lift, LinearMap, LinearMap.ext, toLinearMap, toLinearMap.flip
-/
def foldr (f : M ->ₗ[R] N ->ₗ[R] N) (hf : forall m x, f m (f m x) = Q m • x) :
    N ->ₗ[R] CliffordAlgebra Q ->ₗ[R] N :=
  (CliffordAlgebra.lift Q ⟨f, fun v => LinearMap.ext <| hf v⟩).toLinearMap.flip

@[simp]
/--
theorem `foldr_ι` / 定理 `foldr_ι`

English:
theorem foldr_ι
  given: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (m : M)
  statement: foldr Q f hf n (ι Q m) = f m n
  proof: LinearMap.congr_fun (lift_ι_apply _ _ _) n

@[simp]

中文:
定理 foldr_ι
  条件: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (m : M)
  结论: foldr Q f hf n (ι Q m) = f m n
  证明: LinearMap.congr_fun (lift_ι_apply _ _ _) n

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun
-/
theorem foldr_ι (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (m : M) : foldr Q f hf n (ι Q m) = f m n :=
  LinearMap.congr_fun (lift_ι_apply _ _ _) n

@[simp]
/--
theorem `foldr_algebraMap` / 定理 `foldr_algebraMap`

English:
theorem foldr_algebraMap
  given: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (r : R)
  proof: LinearMap.congr_fun (AlgHom.commutes _ r) n

@[simp]

中文:
定理 foldr_algebraMap
  条件: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (r : R)
  证明: LinearMap.congr_fun (AlgHom.commutes _ r) n

@[simp]

Depends on / 依赖: AlgHom, AlgHom.commutes, LinearMap, LinearMap.congr_fun, commutes, congr_fun
-/
theorem foldr_algebraMap (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (r : R) :
    foldr Q f hf n (algebraMap R _ r) = r • n :=
  LinearMap.congr_fun (AlgHom.commutes _ r) n

@[simp]
/--
theorem `foldr_one` / 定理 `foldr_one`

English:
theorem foldr_one
  given: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N)
  statement: foldr Q f hf n 1 = n
  proof: LinearMap.congr_fun (map_one (lift Q _)) n

@[simp]

中文:
定理 foldr_one
  条件: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N)
  结论: foldr Q f hf n 1 = n
  证明: LinearMap.congr_fun (map_one (lift Q _)) n

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, map_one
-/
theorem foldr_one (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) : foldr Q f hf n 1 = n :=
  LinearMap.congr_fun (map_one (lift Q _)) n

@[simp]
/--
theorem `foldr_mul` / 定理 `foldr_mul`

English:
theorem foldr_mul
  given: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q)
  proof: LinearMap.congr_fun (map_mul (lift Q _) _ _) n

中文:
定理 foldr_mul
  条件: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q)
  证明: LinearMap.congr_fun (map_mul (lift Q _) _ _) n

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun, map_mul
-/
theorem foldr_mul (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q) :
    foldr Q f hf n (a * b) = foldr Q f hf (foldr Q f hf n b) a :=
  LinearMap.congr_fun (map_mul (lift Q _) _ _) n

/--
theorem `foldr_prod_map_ι` / 定理 `foldr_prod_map_ι`

English:
theorem foldr_prod_map_ι
  given: (l : List M) (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N)
  proof: by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, List.foldr_nil, foldr_one]
  | cons hd tl ih => rw [List.map_cons, List.prod_cons, List.foldr_cons, foldr_mul, foldr_ι, ih]

中文:
定理 foldr_prod_map_ι
  条件: (l : List M) (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N)
  证明: by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, List.foldr_nil, foldr_one]
  | cons hd tl ih => rw [List.map_cons, List.prod_cons, List.foldr_cons, foldr_mul, foldr_ι, ih]

Depends on / 依赖: List.foldr_cons, List.foldr_nil, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, foldr_cons, foldr_mul, foldr_nil, foldr_one, map_cons, map_nil, prod_cons, prod_nil
-/
theorem foldr_prod_map_ι (l : List M) (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) :
    foldr Q f hf n (l.map <| ι Q).prod = List.foldr (fun m n => f m n) n l := by
  induction l with
  | nil => rw [List.map_nil, List.prod_nil, List.foldr_nil, foldr_one]
  | cons hd tl ih => rw [List.map_cons, List.prod_cons, List.foldr_cons, foldr_mul, foldr_ι, ih]

end Foldr

section Foldl

/--
Definition of `foldl` / `foldl` 的定义

English:
definition foldl
  signature: (f : M ->ₗ[R] N ->ₗ[R] N) (hf : forall m x, f m (f m x) = Q m • x)
  body: LinearMap.compl₂ (foldr Q f hf) reverse

@[simp]

中文:
定义 foldl
  签名: (f : M ->ₗ[R] N ->ₗ[R] N) (hf : 对任意 m x, f m (f m x) = Q m • x)
  定义体: LinearMap.compl₂ (foldr Q f hf) reverse

@[simp]

Depends on / 依赖: LinearMap, LinearMap.compl, reverse
-/
def foldl (f : M ->ₗ[R] N ->ₗ[R] N) (hf : forall m x, f m (f m x) = Q m • x) :
    N ->ₗ[R] CliffordAlgebra Q ->ₗ[R] N :=
  LinearMap.compl₂ (foldr Q f hf) reverse

@[simp]
/--
theorem `foldl_reverse` / 定理 `foldl_reverse`

English:
theorem foldl_reverse
  given: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q)
  proof: DFunLike.congr_arg (foldr Q f hf n) reverse_reverse _

@[simp]

中文:
定理 foldl_reverse
  条件: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q)
  证明: DFunLike.congr_arg (foldr Q f hf n) reverse_reverse _

@[simp]

Depends on / 依赖: DFunLike, DFunLike.congr_arg, congr_arg, reverse_reverse
-/
theorem foldl_reverse (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q) :
    foldl Q f hf n (reverse x) = foldr Q f hf n x :=
DFunLike.congr_arg (foldr Q f hf n) reverse_reverse _

@[simp]
/--
theorem `foldr_reverse` / 定理 `foldr_reverse`

English:
theorem foldr_reverse
  given: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q)
  proof: rfl

@[simp]

中文:
定理 foldr_reverse
  条件: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q)
  证明: rfl

@[simp]
-/
theorem foldr_reverse (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (x : CliffordAlgebra Q) :
    foldr Q f hf n (reverse x) = foldl Q f hf n x :=
  rfl

@[simp]
/--
theorem `foldl_ι` / 定理 `foldl_ι`

English:
theorem foldl_ι
  given: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (m : M)
  statement: foldl Q f hf n (ι Q m) = f m n
  proof: by
  rw [← foldr_reverse]; rw [reverse_ι]; rw [foldr_ι]

@[simp]

中文:
定理 foldl_ι
  条件: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (m : M)
  结论: foldl Q f hf n (ι Q m) = f m n
  证明: by
  rw [← foldr_reverse]; rw [reverse_ι]; rw [foldr_ι]

@[simp]

Depends on / 依赖: foldr_reverse
-/
theorem foldl_ι (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (m : M) : foldl Q f hf n (ι Q m) = f m n := by
  rw [← foldr_reverse]; rw [reverse_ι]; rw [foldr_ι]

@[simp]
/--
theorem `foldl_algebraMap` / 定理 `foldl_algebraMap`

English:
theorem foldl_algebraMap
  given: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (r : R)
  proof: by
  rw [← foldr_reverse]; rw [reverse.commutes]; rw [foldr_algebraMap]

@[simp]

中文:
定理 foldl_algebraMap
  条件: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (r : R)
  证明: by
  rw [← foldr_reverse]; rw [reverse.commutes]; rw [foldr_algebraMap]

@[simp]

Depends on / 依赖: commutes, foldr_algebraMap, foldr_reverse, reverse, reverse.commutes
-/
theorem foldl_algebraMap (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (r : R) :
    foldl Q f hf n (algebraMap R _ r) = r • n := by
  rw [← foldr_reverse]; rw [reverse.commutes]; rw [foldr_algebraMap]

@[simp]
/--
theorem `foldl_one` / 定理 `foldl_one`

English:
theorem foldl_one
  given: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N)
  statement: foldl Q f hf n 1 = n
  proof: by
  rw [← foldr_reverse]; rw [reverse.map_one]; rw [foldr_one]

@[simp]

中文:
定理 foldl_one
  条件: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N)
  结论: foldl Q f hf n 1 = n
  证明: by
  rw [← foldr_reverse]; rw [reverse.map_one]; rw [foldr_one]

@[simp]

Depends on / 依赖: foldr_one, foldr_reverse, map_one, reverse, reverse.map_one
-/
theorem foldl_one (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) : foldl Q f hf n 1 = n := by
  rw [← foldr_reverse]; rw [reverse.map_one]; rw [foldr_one]

@[simp]
/--
theorem `foldl_mul` / 定理 `foldl_mul`

English:
theorem foldl_mul
  given: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q)
  proof: by
  rw [← foldr_reverse]; rw [← foldr_reverse]; rw [← foldr_reverse]; rw [reverse.map_mul]; rw [foldr_mul]

中文:
定理 foldl_mul
  条件: (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q)
  证明: by
  rw [← foldr_reverse]; rw [← foldr_reverse]; rw [← foldr_reverse]; rw [reverse.map_mul]; rw [foldr_mul]

Depends on / 依赖: foldr_mul, foldr_reverse, map_mul, reverse, reverse.map_mul
-/
theorem foldl_mul (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) (a b : CliffordAlgebra Q) :
    foldl Q f hf n (a * b) = foldl Q f hf (foldl Q f hf n a) b := by
  rw [← foldr_reverse]; rw [← foldr_reverse]; rw [← foldr_reverse]; rw [reverse.map_mul]; rw [foldr_mul]

/--
theorem `foldl_prod_map_ι` / 定理 `foldl_prod_map_ι`

English:
theorem foldl_prod_map_ι
  given: (l : List M) (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N)
  proof: by
  rw [← foldr_reverse]; rw [reverse_prod_map_ι]; rw [← List.map_reverse]; rw [foldr_prod_map_ι]; rw [List.foldr_reverse]

中文:
定理 foldl_prod_map_ι
  条件: (l : List M) (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N)
  证明: by
  rw [← foldr_reverse]; rw [reverse_prod_map_ι]; rw [← List.map_reverse]; rw [foldr_prod_map_ι]; rw [List.foldr_reverse]

Depends on / 依赖: List.foldr_reverse, List.map_reverse, foldr_reverse, map_reverse
-/
theorem foldl_prod_map_ι (l : List M) (f : M ->ₗ[R] N ->ₗ[R] N) (hf) (n : N) :
    foldl Q f hf n (l.map <| ι Q).prod = List.foldl (fun m n => f n m) n l := by
  rw [← foldr_reverse]; rw [reverse_prod_map_ι]; rw [← List.map_reverse]; rw [foldr_prod_map_ι]; rw [List.foldr_reverse]

end Foldl

@[elab_as_elim]
/--
theorem `right_induction` / 定理 `right_induction`

English:
theorem right_induction
  statement: {P : CliffordAlgebra Q -> Prop} (algebraMap : forall r : R, P (algebraMap _ _ r))
  proof: by
  /- It would be neat if we could prove this via `foldr` like how we prove
    `CliffordAlgebra.induction`, but going via the grading seems easier. -/
  intro x
  have : x in ⊤ := Submodule.mem_top (R := R)
  rw [← iSup_ι_range_eq_top] at this
  induction this using Submodule.iSup_induction' with

中文:
定理 right_induction
  结论: {P : CliffordAlgebra Q -> 命题} (algebraMap : 对任意 r : R, P (algebraMap _ _ r))
  证明: by
  /- It would be neat if we could prove this via `foldr` like how we prove
    `CliffordAlgebra.induction`, but going via the grading seems easier. -/
  intro x
  have : x in ⊤ := Submodule.mem_top (R := R)
  rw [← iSup_ι_range_eq_top] at this
  induction this using Submodule.iSup_induction' with
-/
theorem right_induction {P : CliffordAlgebra Q -> Prop} (algebraMap : forall r : R, P (algebraMap _ _ r))
    (add : forall x y, P x -> P y -> P (x + y)) (mul_ι : forall m x, P x -> P (x * ι Q m)) : forall x, P x := by
  /- It would be neat if we could prove this via `foldr` like how we prove
    `CliffordAlgebra.induction`, but going via the grading seems easier. -/
  intro x
  have : x in ⊤ := Submodule.mem_top (R := R)
  rw [← iSup_ι_range_eq_top] at this
  induction this using Submodule.iSup_induction' with
  | mem i x hx =>
    induction hx using Submodule.pow_induction_on_right' with
    | algebraMap r => exact algebraMap r
    | add _x _y _i _ _ ihx ihy => exact add _ _ ihx ihy
    | mul_mem _i x _hx px m hm =>
      obtain ⟨m, rfl⟩ := hm
      exact mul_ι _ _ px
  | zero => simpa only [map_zero] using algebraMap 0
  | add _x _y _ _ ihx ihy =>
    exact add _ _ ihx ihy

@[elab_as_elim]
/--
theorem `left_induction` / 定理 `left_induction`

English:
theorem left_induction
  statement: {P : CliffordAlgebra Q -> Prop} (algebraMap : forall r : R, P (algebraMap _ _ r))
  proof: by
  refine reverse_involutive.surjective.forall.2 ?_
  intro x
  induction x using CliffordAlgebra.right_induction with
  | algebraMap r => simpa only [reverse.commutes] using algebraMap r
  | add _ _ hx hy => simpa only [map_add] using add _ _ hx hy
  | mul_ι _ _ hx => simpa only [reverse.map_mul,

中文:
定理 left_induction
  结论: {P : CliffordAlgebra Q -> 命题} (algebraMap : 对任意 r : R, P (algebraMap _ _ r))
  证明: by
  refine reverse_involutive.surjective.forall.2 ?_
  intro x
  induction x using CliffordAlgebra.right_induction with
  | algebraMap r => simpa only [reverse.commutes] using algebraMap r
  | add _ _ hx hy => simpa only [map_add] using add _ _ hx hy
  | mul_ι _ _ hx => simpa only [reverse.map_mul,

Depends on / 依赖: CliffordAlgebra, CliffordAlgebra.right_induction, algebraMap, commutes, map_add, map_mul, reverse, reverse.commutes, reverse.map_mul, reverse_involutive, reverse_involutive.surjective.forall, right_induction, surjective
-/
theorem left_induction {P : CliffordAlgebra Q -> Prop} (algebraMap : forall r : R, P (algebraMap _ _ r))
    (add : forall x y, P x -> P y -> P (x + y)) (ι_mul : forall x m, P x -> P (ι Q m * x)) : forall x, P x := by
  refine reverse_involutive.surjective.forall.2 ?_
  intro x
  induction x using CliffordAlgebra.right_induction with
  | algebraMap r => simpa only [reverse.commutes] using algebraMap r
  | add _ _ hx hy => simpa only [map_add] using add _ _ hx hy
  | mul_ι _ _ hx => simpa only [reverse.map_mul, reverse_ι] using ι_mul _ _ hx

/-! ### Versions with extra state -/


/--
Definition of `foldr'Aux` / `foldr'Aux` 的定义

English:
definition foldr'Aux
  signature: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  body: by
  have v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  have l := v_mul.compl₂ (LinearMap.fst _ _ N)
  exact
    { toFun := fun m => (l m).prod (f m)
      map_add' := fun v₂ v₂ =>
        LinearMap.ext fun x =>
          Prod.ext (LinearMap.congr_fun (l.map_add _ _) x) (LinearM

中文:
定义 foldr'Aux
  签名: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  定义体: by
  have v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  have l := v_mul.compl₂ (LinearMap.fst _ _ N)
  exact
    { toFun := fun m => (l m).prod (f m)
      map_add' := fun v₂ v₂ =>
        LinearMap.ext fun x =>
          Prod.ext (LinearMap.congr_fun (l.map_add _ _) x) (LinearM

Depends on / 依赖: Algebra, Algebra.lmul, CliffordAlgebra, LinearMap, LinearMap.congr_fun, LinearMap.ext, LinearMap.fst, Prod.ext, congr_fun, f.map_add, f.map_smul, l.map_add, l.map_smul, map_add, map_smul, toLinearMap, v_mul, v_mul.compl
-/
def foldr'Aux (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N) :
    M ->ₗ[R] Module.End R (CliffordAlgebra Q × N) := by
  have v_mul := (Algebra.lmul R (CliffordAlgebra Q)).toLinearMap ∘ₗ ι Q
  have l := v_mul.compl₂ (LinearMap.fst _ _ N)
  exact
    { toFun := fun m => (l m).prod (f m)
      map_add' := fun v₂ v₂ =>
        LinearMap.ext fun x =>
          Prod.ext (LinearMap.congr_fun (l.map_add _ _) x) (LinearMap.congr_fun (f.map_add _ _) x)
      map_smul' := fun c v =>
        LinearMap.ext fun x =>
          Prod.ext (LinearMap.congr_fun (l.map_smul _ _) x)
            (LinearMap.congr_fun (f.map_smul _ _) x) }

/--
theorem `foldr'Aux_apply_apply` / 定理 `foldr'Aux_apply_apply`

English:
theorem foldr'Aux_apply_apply
  given: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N) (m : M) (x_fx)
  proof: rfl

中文:
定理 foldr'Aux_apply_apply
  条件: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N) (m : M) (x_fx)
  证明: rfl
-/
theorem foldr'Aux_apply_apply (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N) (m : M) (x_fx) :
    foldr'Aux Q f m x_fx = (ι Q m * x_fx.1, f m x_fx) :=
  rfl

/--
theorem `foldr'Aux_foldr'Aux` / 定理 `foldr'Aux_foldr'Aux`

English:
theorem foldr'Aux_foldr'Aux
  statement: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  proof: by
  simp only [foldr'Aux_apply_apply]
  rw [← mul_assoc]; rw [ι_sq_scalar]; rw [← Algebra.smul_def]; rw [hf]; rw [Prod.smul_mk]

中文:
定理 foldr'Aux_foldr'Aux
  结论: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  证明: by
  simp only [foldr'Aux_apply_apply]
  rw [← mul_assoc]; rw [ι_sq_scalar]; rw [← Algebra.smul_def]; rw [hf]; rw [Prod.smul_mk]
-/
theorem foldr'Aux_foldr'Aux (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
    (hf : forall m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (v : M) (x_fx) :
    foldr'Aux Q f v (foldr'Aux Q f v x_fx) = Q v • x_fx := by
  simp only [foldr'Aux_apply_apply]
  rw [← mul_assoc]; rw [ι_sq_scalar]; rw [← Algebra.smul_def]; rw [hf]; rw [Prod.smul_mk]

/--
Definition of `foldr'` / `foldr'` 的定义

English:
definition foldr'
  signature: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  body: LinearMap.snd _ _ _ ∘ₗ foldr Q (foldr'Aux Q f) (foldr'Aux_foldr'Aux Q _ hf) (1, n)

中文:
定义 foldr'
  签名: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  定义体: LinearMap.snd _ _ _ ∘ₗ foldr Q (foldr'Aux Q f) (foldr'Aux_foldr'Aux Q _ hf) (1, n)
-/
def foldr' (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
    (hf : forall m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n : N) : CliffordAlgebra Q ->ₗ[R] N :=
  LinearMap.snd _ _ _ ∘ₗ foldr Q (foldr'Aux Q f) (foldr'Aux_foldr'Aux Q _ hf) (1, n)

/--
theorem `foldr'_algebraMap` / 定理 `foldr'_algebraMap`

English:
theorem foldr'_algebraMap
  statement: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  proof: congr_arg Prod.snd (foldr_algebraMap _ _ _ _ _)

中文:
定理 foldr'_algebraMap
  结论: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  证明: congr_arg Prod.snd (foldr_algebraMap _ _ _ _ _)
-/
theorem foldr'_algebraMap (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
    (hf : forall m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n r) :
    foldr' Q f hf n (algebraMap R _ r) = r • n :=
  congr_arg Prod.snd (foldr_algebraMap _ _ _ _ _)

/--
theorem `foldr'_ι` / 定理 `foldr'_ι`

English:
theorem foldr'_ι
  statement: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  proof: congr_arg Prod.snd (foldr_ι _ _ _ _ _)

中文:
定理 foldr'_ι
  结论: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  证明: congr_arg Prod.snd (foldr_ι _ _ _ _ _)
-/
theorem foldr'_ι (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
    (hf : forall m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) :
    foldr' Q f hf n (ι Q m) = f m (1, n) :=
  congr_arg Prod.snd (foldr_ι _ _ _ _ _)

/--
theorem `foldr'_ι_mul` / 定理 `foldr'_ι_mul`

English:
theorem foldr'_ι_mul
  statement: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  proof: by
  dsimp [foldr']
  rw [foldr_mul]; rw [foldr_ι]; rw [foldr'Aux_apply_apply]
  refine congr_arg (f m) (Prod.mk.eta.symm.trans ?_)
  congr 1
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp_rw [foldr_algebraMap, Prod.smul_mk, Algebra.algebraMap_eq_smul_one]
  | add x

中文:
定理 foldr'_ι_mul
  结论: (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
  证明: by
  dsimp [foldr']
  rw [foldr_mul]; rw [foldr_ι]; rw [foldr'Aux_apply_apply]
  refine congr_arg (f m) (Prod.mk.eta.symm.trans ?_)
  congr 1
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp_rw [foldr_algebraMap, Prod.smul_mk, Algebra.algebraMap_eq_smul_one]
  | add x
-/
theorem foldr'_ι_mul (f : M ->ₗ[R] CliffordAlgebra Q × N ->ₗ[R] N)
    (hf : forall m x fx, f m (ι Q m * x, f m (x, fx)) = Q m • fx) (n m) (x) :
    foldr' Q f hf n (ι Q m * x) = f m (x, foldr' Q f hf n x) := by
  dsimp [foldr']
  rw [foldr_mul]; rw [foldr_ι]; rw [foldr'Aux_apply_apply]
  refine congr_arg (f m) (Prod.mk.eta.symm.trans ?_)
  congr 1
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp_rw [foldr_algebraMap, Prod.smul_mk, Algebra.algebraMap_eq_smul_one]
  | add x y hx hy => rw [map_add, Prod.fst_add, hx, hy]
  | ι_mul m x hx => rw [foldr_mul, foldr_ι, foldr'Aux_apply_apply, hx]

end CliffordAlgebra
