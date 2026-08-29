/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Yaël Dillies
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Perfect pairings

This file defines perfect pairings of modules.

A perfect pairing of two (left) modules may be defined either as:
1. A bilinear map `M × N → R` such that the induced maps `M → Dual R N` and `N → Dual R M` are both
  bijective. It follows from this that both `M` and `N` are reflexive modules.
2. A linear equivalence `N ≃ Dual R M` for which `M` is reflexive. (It then follows that `N` is
  reflexive.)

In this file we provide a definition `IsPerfPair` corresponding to 1 above, together with logic
to connect 1 and 2.
-/

@[expose] public section

open Function Module

namespace LinearMap
variable {R K M M' N N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M']
  [AddCommGroup N']

section CommRing
variable [CommRing R] [Module R M] [Module R M'] [Module R N] [Module R N']
  {p : M ->ₗ[R] N ->ₗ[R] R} {x : M} {y : N}

/-- For a ring `R` and two modules `M` and `N`, a perfect pairing is a bilinear map `M × N → R`
that is bijective in both arguments. -/
@[ext]
/--
Definition of `IsPerfPair` / `IsPerfPair` 的定义

English:
class IsPerfPair
  parameters: (p : M ->ₗ[R] N ->ₗ[R] R)
  axioms and operations (2):
    - bijective_left((p)) : Bijective p
    - bijective_right((p)) : Bijective p.flip

中文:
类 是PerfPair
  参数: (p : M ->ₗ[R] N ->ₗ[R] R)
  公理与运算 (2 个):
    - bijective_left((p)) : 双射 p
    - bijective_right((p)) : 双射 p.flip

Depends on / 依赖: IsPerfPair, IsPerfPair.bijective_right, bijective_right
-/
class IsPerfPair (p : M ->ₗ[R] N ->ₗ[R] R) where
  bijective_left (p) : Bijective p
  bijective_right (p) : Bijective p.flip

/--
lemma `IsPerfPair.flip` / 引理 `IsPerfPair.flip`

English:
lemma IsPerfPair.flip
  given: (hp : p.IsPerfPair)
  statement: p.flip.IsPerfPair where
  proof: IsPerfPair.bijective_right p
  bijective_right := IsPerfPair.bijective_left p

中文:
引理 是PerfPair.flip
  条件: (hp : p.是PerfPair)
  结论: p.flip.是PerfPair where
  证明: IsPerfPair.bijective_right p
  bijective_right := IsPerfPair.bijective_left p
-/
protected lemma IsPerfPair.flip (hp : p.IsPerfPair) : p.flip.IsPerfPair where
  bijective_left := IsPerfPair.bijective_right p
  bijective_right := IsPerfPair.bijective_left p

variable [p.IsPerfPair]

/--
Instance `flip.instIsPerfPair` / 实例 `flip.instIsPerfPair`

English:
instance flip.instIsPerfPair
  signature: : p.flip.IsPerfPair
  body: .flip ‹_›

中文:
实例 flip.instIsPerfPair
  签名: : p.flip.是PerfPair
  定义体: .flip ‹_›
-/
instance flip.instIsPerfPair : p.flip.IsPerfPair := .flip ‹_›

variable (p)

/--
Definition of `toPerfPair` / `toPerfPair` 的定义

English:
definition toPerfPair
  signature: : M ≃ₗ[R] Dual R N
  body: .ofBijective { toFun := _, map_add' x y := by simp, map_smul' r x := by simp }
    IsPerfPair.bijective_left p

中文:
定义 toPerfPair
  签名: : M ≃ₗ[R] 对偶 R N
  定义体: .ofBijective { toFun := _, map_add' x y := by simp, map_smul' r x := by simp }
    IsPerfPair.bijective_left p

Depends on / 依赖: IsPerfPair, IsPerfPair.bijective_left, bijective_left, map_add, map_smul, ofBijective
-/
noncomputable def toPerfPair : M ≃ₗ[R] Dual R N :=
.ofBijective { toFun := _, map_add' x y := by simp, map_smul' r x := by simp }
    IsPerfPair.bijective_left p

/--
lemma `toLinearMap_toPerfPair` / 引理 `toLinearMap_toPerfPair`

English:
lemma toLinearMap_toPerfPair
  given: (x : M)
  statement: p.toPerfPair x = p x
  proof: rfl

中文:
引理 toLinearMap_toPerfPair
  条件: (x : M)
  结论: p.toPerfPair x = p x
  证明: rfl
-/
@[simp] lemma toLinearMap_toPerfPair (x : M) : p.toPerfPair x = p x := rfl
/--
lemma `toPerfPair_apply` / 引理 `toPerfPair_apply`

English:
lemma toPerfPair_apply
  given: (x : M) (y : N)
  statement: p.toPerfPair x y = p x y
  proof: rfl

中文:
引理 toPerfPair_apply
  条件: (x : M) (y : N)
  结论: p.toPerfPair x y = p x y
  证明: rfl
-/
@[simp] lemma toPerfPair_apply (x : M) (y : N) : p.toPerfPair x y = p x y := rfl

/--
lemma `apply_symm_toPerfPair_self` / 引理 `apply_symm_toPerfPair_self`

English:
lemma apply_symm_toPerfPair_self
  given: (f : Dual R N)
  statement: p (p.toPerfPair.symm f) = f
  proof: p.toPerfPair.apply_symm_apply f

中文:
引理 apply_symm_toPerfPair_self
  条件: (f : 对偶 R N)
  结论: p (p.toPerfPair.symm f) = f
  证明: p.toPerfPair.apply_symm_apply f
-/
@[simp] lemma apply_symm_toPerfPair_self (f : Dual R N) : p (p.toPerfPair.symm f) = f :=
  p.toPerfPair.apply_symm_apply f

/--
lemma `apply_toPerfPair_flip` / 引理 `apply_toPerfPair_flip`

English:
lemma apply_toPerfPair_flip
  given: (f : Dual R M) (x : M)
  statement: p x (p.flip.toPerfPair.symm f) = f x
  proof: congr($(p.flip.apply_symm_toPerfPair_self ..) x)

include p in

中文:
引理 apply_toPerfPair_flip
  条件: (f : 对偶 R M) (x : M)
  结论: p x (p.flip.toPerfPair.symm f) = f x
  证明: congr($(p.flip.apply_symm_toPerfPair_self ..) x)

include p in
-/
@[simp] lemma apply_toPerfPair_flip (f : Dual R M) (x : M) : p x (p.flip.toPerfPair.symm f) = f x :=
  congr($(p.flip.apply_symm_toPerfPair_self ..) x)

include p in
/--
lemma `_root_.Module.IsReflexive.of_isPerfPair` / 引理 `_root_.Module.IsReflexive.of_isPerfPair`

English:
lemma _root_.Module.IsReflexive.of_isPerfPair
  statement: IsReflexive R M where
  proof: by
    convert! (p.toPerfPair.trans p.flip.toPerfPair.dualMap.symm).bijective
    ext x f
    simp

include p in

中文:
引理 _root_.模.是自反.of_isPerfPair
  结论: 是自反 R M where
  证明: by
    convert! (p.toPerfPair.trans p.flip.toPerfPair.dualMap.symm).bijective
    ext x f
    simp

include p in

Depends on / 依赖: bijective, convert, dualMap, p.flip.toPerfPair.dualMap.symm, p.toPerfPair.trans, toPerfPair
-/
lemma _root_.Module.IsReflexive.of_isPerfPair : IsReflexive R M where
  bijective_dual_eval' := by
    convert! (p.toPerfPair.trans p.flip.toPerfPair.dualMap.symm).bijective
    ext x f
    simp

include p in
/--
lemma `_root_.Module.finrank_of_isPerfPair` / 引理 `_root_.Module.finrank_of_isPerfPair`

English:
lemma _root_.Module.finrank_of_isPerfPair
  given: [Module.Finite R M] [Module.Free R M]
  proof: ((Module.Free.chooseBasis R M).toDualEquiv.trans p.flip.toPerfPair.symm).finrank_eq

中文:
引理 _root_.模.finrank_of_isPerfPair
  条件: [模.有限 R M] [模.自由 R M]
  证明: ((Module.Free.chooseBasis R M).toDualEquiv.trans p.flip.toPerfPair.symm).finrank_eq

Depends on / 依赖: Module, Module.Free.chooseBasis, chooseBasis, finrank_eq, p.flip.toPerfPair.symm, toDualEquiv, toDualEquiv.trans, toPerfPair
-/
lemma _root_.Module.finrank_of_isPerfPair [Module.Finite R M] [Module.Free R M] :
    finrank R M = finrank R N :=
  ((Module.Free.chooseBasis R M).toDualEquiv.trans p.flip.toPerfPair.symm).finrank_eq

/--
Instance `IsPerfPair.id` / 实例 `IsPerfPair.id`

English:
instance IsPerfPair.id
  signature: [IsReflexive R M]
  body: bijective_id
  bijective_right := bijective_dual_eval R M

中文:
实例 是PerfPair.id
  签名: [是自反 R M]
  定义体: bijective_id
  bijective_right := bijective_dual_eval R M
-/
protected instance IsPerfPair.id [IsReflexive R M] : IsPerfPair (.id (R := R) (M := Dual R M)) where
  bijective_left := bijective_id
  bijective_right := bijective_dual_eval R M

/--
Instance `IsPerfPair.dualEval` / 实例 `IsPerfPair.dualEval`

English:
instance IsPerfPair.dualEval
  signature: [IsReflexive R M]
  body: .flip .id

中文:
实例 是PerfPair.dualEval
  签名: [是自反 R M]
  定义体: .flip .id
-/
instance IsPerfPair.dualEval [IsReflexive R M] : IsPerfPair (Dual.eval R M) := .flip .id

/--
Instance `IsPerfPair.compl₁₂` / 实例 `IsPerfPair.compl₁₂`

English:
instance IsPerfPair.compl₁₂
  signature: (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N)
  body: ⟨((LinearEquiv.congrLeft R R eN).symm.bijective.comp
    (IsPerfPair.bijective_left p)).comp eM.bijective,
    ((LinearEquiv.congrLeft R R eM).symm.bijective.comp
    (IsPerfPair.bijective_right p)).comp eN.bijective⟩

中文:
实例 是PerfPair.compl₁₂
  签名: (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N)
  定义体: ⟨((LinearEquiv.congrLeft R R eN).symm.bijective.comp
    (IsPerfPair.bijective_left p)).comp eM.bijective,
    ((LinearEquiv.congrLeft R R eM).symm.bijective.comp
    (IsPerfPair.bijective_right p)).comp eN.bijective⟩

Depends on / 依赖: IsPerfPair, IsPerfPair.bijective_left, IsPerfPair.bijective_right, LinearEquiv, LinearEquiv.congrLeft, bijective, bijective_left, bijective_right, congrLeft, eM.bijective, eN.bijective, symm.bijective.comp
-/
instance IsPerfPair.compl₁₂ (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) :
    (p.compl₁₂ eM eN : M' ->ₗ[R] N' ->ₗ[R] R).IsPerfPair :=
  ⟨((LinearEquiv.congrLeft R R eN).symm.bijective.comp
    (IsPerfPair.bijective_left p)).comp eM.bijective,
    ((LinearEquiv.congrLeft R R eM).symm.bijective.comp
    (IsPerfPair.bijective_right p)).comp eN.bijective⟩

/--
lemma `IsPerfPair.congr` / 引理 `IsPerfPair.congr`

English:
lemma IsPerfPair.congr
  statement: (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) (q : M' ->ₗ[R] N' ->ₗ[R] R)
  proof: by
  obtain rfl : q = p.compl₁₂ eM eN := by subst H; ext; simp
  infer_instance

中文:
引理 是PerfPair.congr
  结论: (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) (q : M' ->ₗ[R] N' ->ₗ[R] R)
  证明: by
  obtain rfl : q = p.compl₁₂ eM eN := by subst H; ext; simp
  infer_instance

Depends on / 依赖: infer_instance, p.compl
-/
lemma IsPerfPair.congr (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) (q : M' ->ₗ[R] N' ->ₗ[R] R)
    (H : q.compl₁₂ eM.symm eN.symm = p) : q.IsPerfPair := by
  obtain rfl : q = p.compl₁₂ eM eN := by subst H; ext; simp
  infer_instance

/--
lemma `IsPerfPair.of_bijective` / 引理 `IsPerfPair.of_bijective`

English:
lemma IsPerfPair.of_bijective
  given: (p : M ->ₗ[R] N ->ₗ[R] R) [IsReflexive R N] (h : Bijective p)
  proof: inferInstanceAs ((LinearMap.id (R := R) (M := Dual R N)).compl₁₂
    (LinearEquiv.ofBijective p h : M ->ₗ[R] N ->ₗ[R] R)
    (LinearEquiv.refl R N : N ->ₗ[R] N)).IsPerfPair

中文:
引理 是PerfPair.of_bijective
  条件: (p : M ->ₗ[R] N ->ₗ[R] R) [是自反 R N] (h : 双射 p)
  证明: inferInstanceAs ((LinearMap.id (R := R) (M := Dual R N)).compl₁₂
    (LinearEquiv.ofBijective p h : M ->ₗ[R] N ->ₗ[R] R)
    (LinearEquiv.refl R N : N ->ₗ[R] N)).IsPerfPair

Depends on / 依赖: IsPerfPair, LinearEquiv, LinearEquiv.ofBijective, LinearEquiv.refl, LinearMap, LinearMap.id, ofBijective
-/
lemma IsPerfPair.of_bijective (p : M ->ₗ[R] N ->ₗ[R] R) [IsReflexive R N] (h : Bijective p) :
    IsPerfPair p :=
  inferInstanceAs ((LinearMap.id (R := R) (M := Dual R N)).compl₁₂
    (LinearEquiv.ofBijective p h : M ->ₗ[R] N ->ₗ[R] R)
    (LinearEquiv.refl R N : N ->ₗ[R] N)).IsPerfPair

end CommRing

section Field
variable [Field K] [Module K M] [Module K N] {p : M ->ₗ[K] N ->ₗ[K] K} {x : M} {y : N}

/--
lemma `IsPerfPair.of_injective` / 引理 `IsPerfPair.of_injective`

English:
lemma IsPerfPair.of_injective
  given: [FiniteDimensional K M] (h : Injective p) (h' : Injective p.flip)
  proof: ⟨h, by rwa [← p.flip_injective_iff₁]⟩
  bijective_right := ⟨h', by
    have : FiniteDimensional K N := FiniteDimensional.of_injective p.flip h'
    rwa [← p.flip.flip_injective_iff₁, LinearMap.flip_flip]⟩

中文:
引理 是PerfPair.of_injective
  条件: [有限维 K M] (h : 单射 p) (h' : 单射 p.flip)
  证明: ⟨h, by rwa [← p.flip_injective_iff₁]⟩
  bijective_right := ⟨h', by
    have : FiniteDimensional K N := FiniteDimensional.of_injective p.flip h'
    rwa [← p.flip.flip_injective_iff₁, LinearMap.flip_flip]⟩

Depends on / 依赖: p.flip_injective_iff
-/
lemma IsPerfPair.of_injective [FiniteDimensional K M] (h : Injective p) (h' : Injective p.flip) :
    p.IsPerfPair where
  bijective_left := ⟨h, by rwa [← p.flip_injective_iff₁]⟩
  bijective_right := ⟨h', by
    have : FiniteDimensional K N := FiniteDimensional.of_injective p.flip h'
    rwa [← p.flip.flip_injective_iff₁, LinearMap.flip_flip]⟩

/--
lemma `IsPerfPair.of_injective'` / 引理 `IsPerfPair.of_injective'`

English:
lemma IsPerfPair.of_injective'
  given: [FiniteDimensional K N] (h : Injective p) (h' : Injective p.flip)
  proof: .flip .of_injective h' h

中文:
引理 是PerfPair.of_injective'
  条件: [有限维 K N] (h : 单射 p) (h' : 单射 p.flip)
  证明: .flip .of_injective h' h

Depends on / 依赖: of_injective
-/
lemma IsPerfPair.of_injective' [FiniteDimensional K N] (h : Injective p) (h' : Injective p.flip) :
p.IsPerfPair := .flip .of_injective h' h

end Field
end LinearMap

noncomputable section

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace LinearMap
variable {p : M ->ₗ[R] N ->ₗ[R] R} [p.IsPerfPair]

variable (p) in
/--
Definition of `IsPerfectCompl` / `IsPerfectCompl` 的定义

English:
structure IsPerfectCompl
  parameters: (U : Submodule R M) (V : Submodule R N)
  axioms and operations (2):
    - isCompl_left : IsCompl U (V.dualAnnihilator.map (p.toPerfPair.symm : Dual R N ->ₗ[R] M))
    - isCompl_right : IsCompl V (U.dualAnnihilator.map (p.flip.toPerfPair.symm : Dual R M ->ₗ[R] N))

中文:
结构 是PerfectCompl
  参数: (U : 子模 R M) (V : 子模 R N)
  公理与运算 (2 个):
    - isCompl_left : 是补集 U (V.dualAnnihilator.map (p.toPerfPair.symm : 对偶 R N ->ₗ[R] M))
    - isCompl_right : 是补集 V (U.dualAnnihilator.map (p.flip.toPerfPair.symm : 对偶 R M ->ₗ[R] N))
-/
structure IsPerfectCompl (U : Submodule R M) (V : Submodule R N) : Prop where
  isCompl_left : IsCompl U (V.dualAnnihilator.map (p.toPerfPair.symm : Dual R N ->ₗ[R] M))
  isCompl_right : IsCompl V (U.dualAnnihilator.map (p.flip.toPerfPair.symm : Dual R M ->ₗ[R] N))

namespace IsPerfectCompl
variable {U : Submodule R M} {V : Submodule R N}

/--
lemma `flip` / 引理 `flip`

English:
lemma flip
  given: (h : p.IsPerfectCompl U V)
  proof: h.isCompl_right
  isCompl_right := h.isCompl_left

@[simp]

中文:
引理 flip
  条件: (h : p.是PerfectCompl U V)
  证明: h.isCompl_right
  isCompl_right := h.isCompl_left

@[simp]
-/
protected lemma flip (h : p.IsPerfectCompl U V) :
    p.flip.IsPerfectCompl V U where
  isCompl_left := h.isCompl_right
  isCompl_right := h.isCompl_left

@[simp]
/--
lemma `flip_iff` / 引理 `flip_iff`

English:
lemma flip_iff
  proof: ⟨fun h => h.flip, fun h => h.flip⟩

@[simp]

中文:
引理 flip_iff
  证明: ⟨fun h => h.flip, fun h => h.flip⟩

@[simp]
-/
protected lemma flip_iff :
    p.flip.IsPerfectCompl V U ↔ p.IsPerfectCompl U V :=
  ⟨fun h => h.flip, fun h => h.flip⟩

@[simp]
/--
lemma `left_top_iff` / 引理 `left_top_iff`

English:
lemma left_top_iff
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
· exact eq_top_of_isCompl_bot by simpa using h.isCompl_right
  · rw [h]
    exact
      { isCompl_left := by simpa using isCompl_top_bot
        isCompl_right := by simpa using isCompl_top_bot }

@[simp]

中文:
引理 left_top_iff
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
· exact eq_top_of_isCompl_bot by simpa using h.isCompl_right
  · rw [h]
    exact
      { isCompl_left := by simpa using isCompl_top_bot
        isCompl_right := by simpa using isCompl_top_bot }

@[simp]

Depends on / 依赖: eq_top_of_isCompl_bot, h.isCompl_right, isCompl_left, isCompl_right, isCompl_top_bot
-/
lemma left_top_iff :
    p.IsPerfectCompl ⊤ V ↔ V = ⊤ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
· exact eq_top_of_isCompl_bot by simpa using h.isCompl_right
  · rw [h]
    exact
      { isCompl_left := by simpa using isCompl_top_bot
        isCompl_right := by simpa using isCompl_top_bot }

@[simp]
/--
lemma `right_top_iff` / 引理 `right_top_iff`

English:
lemma right_top_iff
  proof: by
  rw [← IsPerfectCompl.flip_iff]
  exact left_top_iff

中文:
引理 right_top_iff
  证明: by
  rw [← IsPerfectCompl.flip_iff]
  exact left_top_iff

Depends on / 依赖: IsPerfectCompl, IsPerfectCompl.flip_iff, flip_iff, left_top_iff
-/
lemma right_top_iff :
    p.IsPerfectCompl U ⊤ ↔ U = ⊤ := by
  rw [← IsPerfectCompl.flip_iff]
  exact left_top_iff

end IsPerfectCompl

end LinearMap

variable [IsReflexive R M]

variable (e : N ≃ₗ[R] Dual R M)

namespace LinearEquiv

/--
Definition of `flip` / `flip` 的定义

English:
definition flip
  signature: : M ≃ₗ[R] Dual R N
  body: (evalEquiv R M).trans e.dualMap

中文:
定义 flip
  签名: : M ≃ₗ[R] 对偶 R N
  定义体: (evalEquiv R M).trans e.dualMap

Depends on / 依赖: dualMap, e.dualMap, evalEquiv
-/
def flip : M ≃ₗ[R] Dual R N :=
  (evalEquiv R M).trans e.dualMap

/--
lemma `coe_toLinearMap_flip` / 引理 `coe_toLinearMap_flip`

English:
lemma coe_toLinearMap_flip
  statement: e.flip = (↑e : N ->ₗ[R] Dual R M).flip
  proof: rfl

中文:
引理 coe_toLinearMap_flip
  结论: e.flip = (↑e : N ->ₗ[R] 对偶 R M).flip
  证明: rfl
-/
@[simp] lemma coe_toLinearMap_flip : e.flip = (↑e : N ->ₗ[R] Dual R M).flip := rfl

/--
lemma `flip_apply` / 引理 `flip_apply`

English:
lemma flip_apply
  given: (m : M) (n : N)
  statement: e.flip m n = e n m
  proof: rfl

中文:
引理 flip_apply
  条件: (m : M) (n : N)
  结论: e.flip m n = e n m
  证明: rfl
-/
@[simp] lemma flip_apply (m : M) (n : N) : e.flip m n = e n m := rfl

/--
lemma `symm_flip` / 引理 `symm_flip`

English:
lemma symm_flip
  statement: e.flip.symm = e.symm.dualMap.trans (evalEquiv R M).symm
  proof: rfl

中文:
引理 symm_flip
  结论: e.flip.symm = e.symm.dualMap.trans (evalEquiv R M).symm
  证明: rfl
-/
lemma symm_flip : e.flip.symm = e.symm.dualMap.trans (evalEquiv R M).symm := rfl

/--
lemma `trans_dualMap_symm_flip` / 引理 `trans_dualMap_symm_flip`

English:
lemma trans_dualMap_symm_flip
  statement: e.trans e.flip.symm.dualMap = Dual.eval R N
  proof: by
  ext; simp [symm_flip]

include e in

中文:
引理 trans_dualMap_symm_flip
  结论: e.trans e.flip.symm.dualMap = 对偶.eval R N
  证明: by
  ext; simp [symm_flip]

include e in

Depends on / 依赖: symm_flip
-/
lemma trans_dualMap_symm_flip : e.trans e.flip.symm.dualMap = Dual.eval R N := by
  ext; simp [symm_flip]

include e in
/--
lemma `isReflexive_of_equiv_dual_of_isReflexive` / 引理 `isReflexive_of_equiv_dual_of_isReflexive`

English:
lemma isReflexive_of_equiv_dual_of_isReflexive
  statement: IsReflexive R N
  proof: by
  constructor
  rw [← trans_dualMap_symm_flip e]
  exact LinearEquiv.bijective _

中文:
引理 isReflexive_of_equiv_dual_of_isReflexive
  结论: 是自反 R N
  证明: by
  constructor
  rw [← trans_dualMap_symm_flip e]
  exact LinearEquiv.bijective _

Depends on / 依赖: LinearEquiv, LinearEquiv.bijective, bijective, trans_dualMap_symm_flip
-/
lemma isReflexive_of_equiv_dual_of_isReflexive : IsReflexive R N := by
  constructor
  rw [← trans_dualMap_symm_flip e]
  exact LinearEquiv.bijective _

/--
lemma `flip_flip` / 引理 `flip_flip`

English:
lemma flip_flip
  given: (h : IsReflexive R N := isReflexive_of_equiv_dual_of_isReflexive e)
  proof: by
  ext; rfl

中文:
引理 flip_flip
  条件: (h : 是自反 R N := isReflexive_of_equiv_dual_of_isReflexive e)
  证明: by
  ext; rfl
-/
@[simp] lemma flip_flip (h : IsReflexive R N := isReflexive_of_equiv_dual_of_isReflexive e) :
    e.flip.flip = e := by
  ext; rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: e.toLinearMap.IsPerfPair
  body: e.bijective
  bijective_right := e.flip.bijective

中文:
实例 :
  签名: e.toLinearMap.是PerfPair
  定义体: e.bijective
  bijective_right := e.flip.bijective

Depends on / 依赖: bijective, e.bijective
-/
instance : e.toLinearMap.IsPerfPair where
  bijective_left := e.bijective
  bijective_right := e.flip.bijective

end LinearEquiv

namespace Submodule

open LinearEquiv

omit [IsReflexive R M] in
@[simp]
/--
lemma `dualCoannihilator_map_linearEquiv_flip` / 引理 `dualCoannihilator_map_linearEquiv_flip`

English:
lemma dualCoannihilator_map_linearEquiv_flip
  given: (p : Submodule R M)
  proof: by
  ext; simp

@[simp]

中文:
引理 dualCoannihilator_map_linearEquiv_flip
  条件: (p : 子模 R M)
  证明: by
  ext; simp

@[simp]
-/
lemma dualCoannihilator_map_linearEquiv_flip (p : Submodule R M) :
    (p.map e.toLinearMap.flip).dualCoannihilator =
      p.dualAnnihilator.map (e.symm : Dual R M ->ₗ[R] N) := by
  ext; simp

@[simp]
/--
lemma `map_dualAnnihilator_linearEquiv_flip_symm` / 引理 `map_dualAnnihilator_linearEquiv_flip_symm`

English:
lemma map_dualAnnihilator_linearEquiv_flip_symm
  given: (p : Submodule R N)
  proof: by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← dualCoannihilator_map_linearEquiv_flip]; rw [← LinearEquiv.coe_toLinearMap_flip]; rw [LinearEquiv.flip_flip]

@[simp]

中文:
引理 map_dualAnnihilator_linearEquiv_flip_symm
  条件: (p : 子模 R N)
  证明: by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← dualCoannihilator_map_linearEquiv_flip]; rw [← LinearEquiv.coe_toLinearMap_flip]; rw [LinearEquiv.flip_flip]

@[simp]

Depends on / 依赖: IsReflexive, LinearEquiv, LinearEquiv.coe_toLinearMap_flip, LinearEquiv.flip_flip, coe_toLinearMap_flip, dualCoannihilator_map_linearEquiv_flip, e.isReflexive_of_equiv_dual_of_isReflexive, flip_flip, isReflexive_of_equiv_dual_of_isReflexive
-/
lemma map_dualAnnihilator_linearEquiv_flip_symm (p : Submodule R N) :
    p.dualAnnihilator.map (e.flip.symm : Dual R N ->ₗ[R] M) =
      (p.map (e : N ->ₗ[R] Dual R M)).dualCoannihilator := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← dualCoannihilator_map_linearEquiv_flip]; rw [← LinearEquiv.coe_toLinearMap_flip]; rw [LinearEquiv.flip_flip]

@[simp]
/--
lemma `map_dualCoannihilator_linearEquiv_flip` / 引理 `map_dualCoannihilator_linearEquiv_flip`

English:
lemma map_dualCoannihilator_linearEquiv_flip
  given: (p : Submodule R (Dual R M))
  proof: by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  suffices
      (p.map (e.symm : Dual R M ->ₗ[R] N)).dualAnnihilator.map (e.flip.symm : Dual R N ->ₗ[R] M) =
        (p.dualCoannihilator.map (e.flip : M ->ₗ[R] Dual R N)).map (e.flip.symm : Dual R N ->ₗ[R] M)
    from (Submo

中文:
引理 map_dualCoannihilator_linearEquiv_flip
  条件: (p : 子模 R (对偶 R M))
  证明: by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  suffices
      (p.map (e.symm : Dual R M ->ₗ[R] N)).dualAnnihilator.map (e.flip.symm : Dual R N ->ₗ[R] M) =
        (p.dualCoannihilator.map (e.flip : M ->ₗ[R] Dual R N)).map (e.flip.symm : Dual R N ->ₗ[R] M)
    from (Submo

Depends on / 依赖: IsReflexive, LinearEquiv, LinearEquiv.coe_toLinearMap_flip, LinearEquiv.flip_flip, Submodule, Submodule.map_injective_of_injective, coe_toLinearMap_flip, dualAnnihilator, dualAnnihilator.map, dualCoannihilator, dualCoannihilator_map_linearEquiv_flip, e.flip, e.flip.symm, e.flip.symm.injective, e.isReflexive_of_equiv_dual_of_isReflexive, e.symm, flip_flip, injective, isReflexive_of_equiv_dual_of_isReflexive, map_comp
-/
lemma map_dualCoannihilator_linearEquiv_flip (p : Submodule R (Dual R M)) :
    p.dualCoannihilator.map e.toLinearMap.flip =
      (p.map (e.symm : Dual R M ->ₗ[R] N)).dualAnnihilator := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  suffices
      (p.map (e.symm : Dual R M ->ₗ[R] N)).dualAnnihilator.map (e.flip.symm : Dual R N ->ₗ[R] M) =
        (p.dualCoannihilator.map (e.flip : M ->ₗ[R] Dual R N)).map (e.flip.symm : Dual R N ->ₗ[R] M)
    from (Submodule.map_injective_of_injective e.flip.symm.injective this).symm
  rw [← dualCoannihilator_map_linearEquiv_flip]; rw [← LinearEquiv.coe_toLinearMap_flip]; rw [LinearEquiv.flip_flip]; rw [← map_comp]; rw [← map_comp]
  simp [-coe_toLinearMap_flip]

@[simp]
/--
lemma `dualAnnihilator_map_linearEquiv_flip_symm` / 引理 `dualAnnihilator_map_linearEquiv_flip_symm`

English:
lemma dualAnnihilator_map_linearEquiv_flip_symm
  given: (p : Submodule R (Dual R N))
  proof: by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← map_dualCoannihilator_linearEquiv_flip]; rw [← LinearEquiv.coe_toLinearMap_flip]; rw [LinearEquiv.flip_flip]

中文:
引理 dualAnnihilator_map_linearEquiv_flip_symm
  条件: (p : 子模 R (对偶 R N))
  证明: by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← map_dualCoannihilator_linearEquiv_flip]; rw [← LinearEquiv.coe_toLinearMap_flip]; rw [LinearEquiv.flip_flip]

Depends on / 依赖: IsReflexive, LinearEquiv, LinearEquiv.coe_toLinearMap_flip, LinearEquiv.flip_flip, coe_toLinearMap_flip, e.isReflexive_of_equiv_dual_of_isReflexive, flip_flip, isReflexive_of_equiv_dual_of_isReflexive, map_dualCoannihilator_linearEquiv_flip
-/
lemma dualAnnihilator_map_linearEquiv_flip_symm (p : Submodule R (Dual R N)) :
    (p.map (e.flip.symm : Dual R N ->ₗ[R] M)).dualAnnihilator =
      p.dualCoannihilator.map (e : N ->ₗ[R] Dual R M) := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← map_dualCoannihilator_linearEquiv_flip]; rw [← LinearEquiv.coe_toLinearMap_flip]; rw [LinearEquiv.flip_flip]

end Submodule
