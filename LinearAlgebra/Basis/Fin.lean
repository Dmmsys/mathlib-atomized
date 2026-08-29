/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp, Kevin H. Wilson
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Bases indexed by `Fin`
-/

@[expose] public section

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

namespace Module

open LinearMap

variable {v : ι -> M}
variable [Ring R] [CommRing R₂] [AddCommGroup M]
variable [Module R M] [Module R₂ M]
variable {x y : M}
variable (b : Basis ι R M)

namespace Basis

section Fin

/--
Definition of `mkFinCons` / `mkFinCons` 的定义

English:
definition mkFinCons
  signature: {n : Nat} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
  body: have span_b : N = Submodule.span R (Set.range (N.subtype ∘ b)) := by
    rw [Set.range_comp]; rw [Submodule.span_image]; rw [b.span_eq]; rw [Submodule.map_subtype_top]
  Basis.mk (v := Fin.cons y (N.subtype ∘ b))
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finCons' _ _
      (by
        intro c x hx hc
        rw [← span_b] at hx
        exact hli c x hx hc))
    fun x _ => by simpa [Submodule.mem_span_insert', span_b] using hsp x

@[simp]

中文:
定义 mkFinCons
  签名: {n : 自然数} {N : 子模 R M} (y : M) (b : 基 (有限集 n) R N)
  定义体: have span_b : N = Submodule.span R (Set.range (N.subtype ∘ b)) := by
    rw [Set.range_comp]; rw [Submodule.span_image]; rw [b.span_eq]; rw [Submodule.map_subtype_top]
  Basis.mk (v := Fin.cons y (N.subtype ∘ b))
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finCons' _ _
      (by
        intro c x hx hc
        rw [← span_b] at hx
        exact hli c x hx hc))
    fun x _ => by simpa [Submodule.mem_span_insert', span_b] using hsp x

@[simp]

Depends on / 依赖: Basis.mk, Fin.cons, N.subtype, Set.range, Set.range_comp, Submodule, Submodule.ker_subtype, Submodule.map_subtype_top, Submodule.mem_span_insert, Submodule.span, Submodule.span_image, b.linearIndependent.map, b.span_eq, finCons, ker_subtype, linearIndependent, map_subtype_top, mem_span_insert, range_comp, span_b
-/
noncomputable def mkFinCons {n : Nat} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : forall (c : R), forall x in N, c • y + x = 0 -> c = 0) (hsp : forall z : M, exists c : R, z + c • y in N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : N = Submodule.span R (Set.range (N.subtype ∘ b)) := by
    rw [Set.range_comp]; rw [Submodule.span_image]; rw [b.span_eq]; rw [Submodule.map_subtype_top]
  Basis.mk (v := Fin.cons y (N.subtype ∘ b))
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finCons' _ _
      (by
        intro c x hx hc
        rw [← span_b] at hx
        exact hli c x hx hc))
    fun x _ => by simpa [Submodule.mem_span_insert', span_b] using hsp x

@[simp]
/--
theorem `coe_mkFinCons` / 定理 `coe_mkFinCons`

English:
theorem coe_mkFinCons
  statement: {n : Nat} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
  proof: by
  unfold mkFinCons
  exact coe_mk (v := Fin.cons y (N.subtype ∘ b)) _ _

中文:
定理 coe_mkFinCons
  结论: {n : 自然数} {N : 子模 R M} (y : M) (b : 基 (有限集 n) R N)
  证明: by
  unfold mkFinCons
  exact coe_mk (v := Fin.cons y (N.subtype ∘ b)) _ _

Depends on / 依赖: Fin.cons, N.subtype, coe_mk, mkFinCons, subtype
-/
theorem coe_mkFinCons {n : Nat} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : forall (c : R), forall x in N, c • y + x = 0 -> c = 0) (hsp : forall z : M, exists c : R, z + c • y in N) :
    (mkFinCons y b hli hsp : Fin (n + 1) -> M) = Fin.cons y ((↑) ∘ b) := by
  unfold mkFinCons
  exact coe_mk (v := Fin.cons y (N.subtype ∘ b)) _ _

/--
Definition of `mkFinConsOfLE` / `mkFinConsOfLE` 的定义

English:
definition mkFinConsOfLE
  signature: {n : Nat} {N O : Submodule R M} (y : M) (yO : y in O)
  body: mkFinCons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O -> M) hx))
    fun z => hsp z z.2

@[simp]

中文:
定义 mkFinConsOfLE
  签名: {n : 自然数} {N O : 子模 R M} (y : M) (yO : y in O)
  定义体: mkFinCons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O -> M) hx))
    fun z => hsp z z.2

@[simp]

Depends on / 依赖: Submodule, Submodule.comapSubtypeEquivOfLe, Submodule.mem_comap.mp, b.map, comapSubtypeEquivOfLe, congr_arg, mem_comap, mkFinCons
-/
noncomputable def mkFinConsOfLE {n : Nat} {N O : Submodule R M} (y : M) (yO : y in O)
    (b : Basis (Fin n) R N) (hNO : N <= O) (hli : forall (c : R), forall x in N, c • y + x = 0 -> c = 0)
    (hsp : forall z in O, exists c : R, z + c • y in N) : Basis (Fin (n + 1)) R O :=
  mkFinCons ⟨y, yO⟩ (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm)
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O -> M) hx))
    fun z => hsp z z.2

@[simp]
/--
theorem `coe_mkFinConsOfLE` / 定理 `coe_mkFinConsOfLE`

English:
theorem coe_mkFinConsOfLE
  statement: {n : Nat} {N O : Submodule R M} (y : M) (yO : y in O) (b : Basis (Fin n) R N)
  proof: coe_mkFinCons _ _ _ _

中文:
定理 coe_mkFinConsOfLE
  结论: {n : 自然数} {N O : 子模 R M} (y : M) (yO : y in O) (b : 基 (有限集 n) R N)
  证明: coe_mkFinCons _ _ _ _

Depends on / 依赖: coe_mkFinCons
-/
theorem coe_mkFinConsOfLE {n : Nat} {N O : Submodule R M} (y : M) (yO : y in O) (b : Basis (Fin n) R N)
    (hNO : N <= O) (hli : forall (c : R), forall x in N, c • y + x = 0 -> c = 0)
    (hsp : forall z in O, exists c : R, z + c • y in N) :
    (mkFinConsOfLE y yO b hNO hli hsp : Fin (n + 1) -> O) =
      Fin.cons ⟨y, yO⟩ (Submodule.inclusion hNO ∘ b) :=
  coe_mkFinCons _ _ _ _

/--
Definition of `mkFinSnoc` / `mkFinSnoc` 的定义

English:
definition mkFinSnoc
  signature: {n : Nat} {N : Submodule R M} (b : Basis (Fin n) R N) (y : M)
  body: have span_b : N = Submodule.span R (Set.range (N.subtype ∘ b)) := by
    rw [Set.range_comp]; rw [Submodule.span_image]; rw [b.span_eq]; rw [Submodule.map_subtype_top]
  Basis.mk (v := Fin.snoc (N.subtype ∘ b) y)
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finSnoc' _ _
      (by
        intro c x hx hc
        rw [← span_b] at hx
        exact hli c x hx hc))
    fun x _ => by simpa [Submodule.mem_span_insert', span_b] using hsp x

@[simp]

中文:
定义 mkFinSnoc
  签名: {n : 自然数} {N : 子模 R M} (b : 基 (有限集 n) R N) (y : M)
  定义体: have span_b : N = Submodule.span R (Set.range (N.subtype ∘ b)) := by
    rw [Set.range_comp]; rw [Submodule.span_image]; rw [b.span_eq]; rw [Submodule.map_subtype_top]
  Basis.mk (v := Fin.snoc (N.subtype ∘ b) y)
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finSnoc' _ _
      (by
        intro c x hx hc
        rw [← span_b] at hx
        exact hli c x hx hc))
    fun x _ => by simpa [Submodule.mem_span_insert', span_b] using hsp x

@[simp]

Depends on / 依赖: Basis.mk, Fin.snoc, N.subtype, Set.range, Set.range_comp, Submodule, Submodule.ker_subtype, Submodule.map_subtype_top, Submodule.mem_span_insert, Submodule.span, Submodule.span_image, b.linearIndependent.map, b.span_eq, finSnoc, ker_subtype, linearIndependent, map_subtype_top, mem_span_insert, range_comp, span_b
-/
noncomputable def mkFinSnoc {n : Nat} {N : Submodule R M} (b : Basis (Fin n) R N) (y : M)
    (hli : forall (c : R), forall x in N, c • y + x = 0 -> c = 0) (hsp : forall z : M, exists c : R, z + c • y in N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : N = Submodule.span R (Set.range (N.subtype ∘ b)) := by
    rw [Set.range_comp]; rw [Submodule.span_image]; rw [b.span_eq]; rw [Submodule.map_subtype_top]
  Basis.mk (v := Fin.snoc (N.subtype ∘ b) y)
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finSnoc' _ _
      (by
        intro c x hx hc
        rw [← span_b] at hx
        exact hli c x hx hc))
    fun x _ => by simpa [Submodule.mem_span_insert', span_b] using hsp x

@[simp]
/--
theorem `coe_mkFinSnoc` / 定理 `coe_mkFinSnoc`

English:
theorem coe_mkFinSnoc
  statement: {n : Nat} {N : Submodule R M} (b : Basis (Fin n) R N) (y : M)
  proof: by
  unfold mkFinSnoc
  exact coe_mk (v := Fin.snoc (N.subtype ∘ b) y) _ _

中文:
定理 coe_mkFinSnoc
  结论: {n : 自然数} {N : 子模 R M} (b : 基 (有限集 n) R N) (y : M)
  证明: by
  unfold mkFinSnoc
  exact coe_mk (v := Fin.snoc (N.subtype ∘ b) y) _ _

Depends on / 依赖: Fin.snoc, N.subtype, coe_mk, mkFinSnoc, subtype
-/
theorem coe_mkFinSnoc {n : Nat} {N : Submodule R M} (b : Basis (Fin n) R N) (y : M)
    (hli : forall (c : R), forall x in N, c • y + x = 0 -> c = 0) (hsp : forall z : M, exists c : R, z + c • y in N) :
    (mkFinSnoc b y hli hsp : Fin (n + 1) -> M) = Fin.snoc ((↑) ∘ b) y := by
  unfold mkFinSnoc
  exact coe_mk (v := Fin.snoc (N.subtype ∘ b) y) _ _

/--
Definition of `mkFinSnocOfLE` / `mkFinSnocOfLE` 的定义

English:
definition mkFinSnocOfLE
  signature: {n : Nat} {N O : Submodule R M} (b : Basis (Fin n) R N)
  body: mkFinSnoc (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm) ⟨y, yO⟩
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O -> M) hx))
    fun z => hsp z z.2

@[simp]

中文:
定义 mkFinSnocOfLE
  签名: {n : 自然数} {N O : 子模 R M} (b : 基 (有限集 n) R N)
  定义体: mkFinSnoc (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm) ⟨y, yO⟩
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O -> M) hx))
    fun z => hsp z z.2

@[simp]

Depends on / 依赖: Submodule, Submodule.comapSubtypeEquivOfLe, Submodule.mem_comap.mp, b.map, comapSubtypeEquivOfLe, congr_arg, mem_comap, mkFinSnoc
-/
noncomputable def mkFinSnocOfLE {n : Nat} {N O : Submodule R M} (b : Basis (Fin n) R N)
    (hNO : N <= O) (y : M) (yO : y in O) (hli : forall (c : R), forall x in N, c • y + x = 0 -> c = 0)
    (hsp : forall z in O, exists c : R, z + c • y in N) : Basis (Fin (n + 1)) R O :=
  mkFinSnoc (b.map (Submodule.comapSubtypeEquivOfLe hNO).symm) ⟨y, yO⟩
    (fun c x hc hx => hli c x (Submodule.mem_comap.mp hc) (congr_arg ((↑) : O -> M) hx))
    fun z => hsp z z.2

@[simp]
/--
theorem `coe_mkFinSnocOfLE` / 定理 `coe_mkFinSnocOfLE`

English:
theorem coe_mkFinSnocOfLE
  statement: {n : Nat} {N O : Submodule R M} (b : Basis (Fin n) R N)
  proof: coe_mkFinSnoc _ _ _ _

中文:
定理 coe_mkFinSnocOfLE
  结论: {n : 自然数} {N O : 子模 R M} (b : 基 (有限集 n) R N)
  证明: coe_mkFinSnoc _ _ _ _

Depends on / 依赖: coe_mkFinSnoc
-/
theorem coe_mkFinSnocOfLE {n : Nat} {N O : Submodule R M} (b : Basis (Fin n) R N)
    (hNO : N <= O) (y : M) (yO : y in O) (hli : forall (c : R), forall x in N, c • y + x = 0 -> c = 0)
    (hsp : forall z in O, exists c : R, z + c • y in N) :
    (mkFinSnocOfLE b hNO y yO hli hsp : Fin (n + 1) -> O) =
      Fin.snoc (Submodule.inclusion hNO ∘ b) ⟨y, yO⟩ :=
  coe_mkFinSnoc _ _ _ _

/--
Definition of `finTwoProd` / `finTwoProd` 的定义

English:
definition finTwoProd
  signature: (R : Type*) [Semiring R]
  body: Basis.ofEquivFun (LinearEquiv.finTwoArrow R R).symm

中文:
定义 finTwoProd
  签名: (R : 类型) [半环 R]
  定义体: Basis.ofEquivFun (LinearEquiv.finTwoArrow R R).symm
-/
protected def finTwoProd (R : Type*) [Semiring R] : Basis (Fin 2) R (R × R) :=
  Basis.ofEquivFun (LinearEquiv.finTwoArrow R R).symm

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `finTwoProd_zero` / 定理 `finTwoProd_zero`

English:
theorem finTwoProd_zero
  given: (R : Type*) [Semiring R]
  statement: Basis.finTwoProd R 0 = (1, 0)
  proof: by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

中文:
定理 finTwoProd_zero
  条件: (R : 类型) [半环 R]
  结论: 基.finTwoProd R 0 = (1, 0)
  证明: by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

Depends on / 依赖: Basis.finTwoProd, LinearEquiv, LinearEquiv.finTwoArrow, finTwoArrow, finTwoProd
-/
theorem finTwoProd_zero (R : Type*) [Semiring R] : Basis.finTwoProd R 0 = (1, 0) := by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `finTwoProd_one` / 定理 `finTwoProd_one`

English:
theorem finTwoProd_one
  given: (R : Type*) [Semiring R]
  statement: Basis.finTwoProd R 1 = (0, 1)
  proof: by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

@[simp]

中文:
定理 finTwoProd_one
  条件: (R : 类型) [半环 R]
  结论: 基.finTwoProd R 1 = (0, 1)
  证明: by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

@[simp]

Depends on / 依赖: Basis.finTwoProd, LinearEquiv, LinearEquiv.finTwoArrow, finTwoArrow, finTwoProd
-/
theorem finTwoProd_one (R : Type*) [Semiring R] : Basis.finTwoProd R 1 = (0, 1) := by
  simp [Basis.finTwoProd, LinearEquiv.finTwoArrow]

@[simp]
/--
theorem `coe_finTwoProd_repr` / 定理 `coe_finTwoProd_repr`

English:
theorem coe_finTwoProd_repr
  given: {R : Type*} [Semiring R] (x : R × R)
  proof: rfl

中文:
定理 coe_finTwoProd_repr
  条件: {R : 类型} [半环 R] (x : R × R)
  证明: rfl
-/
theorem coe_finTwoProd_repr {R : Type*} [Semiring R] (x : R × R) :
    ⇑((Basis.finTwoProd R).repr x) = ![x.fst, x.snd] :=
  rfl

end Fin

end Basis

end Module
