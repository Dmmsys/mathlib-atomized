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

/--
theorem `map_nnratCast_smul` / 定理 `map_nnratCast_smul`

English:
theorem map_nnratCast_smul
  statement: [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
  proof: by
  rw [NNRat.cast_def]; rw [NNRat.cast_def]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_smul]; rw [mul_smul]; rw [map_natCast_smul f R S]; rw [map_inv_natCast_smul f R S]

中文:
定理 map_nnratCast_smul
  结论: [AddCommMonoid M] [AddCommMonoid M₂] {F : 类型} [FunLike F M M₂]
  证明: by
  rw [NNRat.cast_def]; rw [NNRat.cast_def]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_smul]; rw [mul_smul]; rw [map_natCast_smul f R S]; rw [map_inv_natCast_smul f R S]

Depends on / 依赖: NNRat.cast_def, cast_def, div_eq_mul_inv, map_inv_natCast_smul, map_natCast_smul, mul_smul
-/
theorem map_nnratCast_smul [AddCommMonoid M] [AddCommMonoid M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionSemiring R] [DivisionSemiring S]
    [Module R M] [Module S M₂] (c : Rat>=0) (x : M) :
    f ((c : R) • x) = (c : S) • f x := by
  rw [NNRat.cast_def]; rw [NNRat.cast_def]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_smul]; rw [mul_smul]; rw [map_natCast_smul f R S]; rw [map_inv_natCast_smul f R S]

/--
theorem `map_ratCast_smul` / 定理 `map_ratCast_smul`

English:
theorem map_ratCast_smul
  statement: [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
  proof: by
  rw [Rat.cast_def]; rw [Rat.cast_def]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_smul]; rw [mul_smul]; rw [map_intCast_smul f R S]; rw [map_inv_natCast_smul f R S]

中文:
定理 map_ratCast_smul
  结论: [AddCommGroup M] [AddCommGroup M₂] {F : 类型} [FunLike F M M₂]
  证明: by
  rw [Rat.cast_def]; rw [Rat.cast_def]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_smul]; rw [mul_smul]; rw [map_intCast_smul f R S]; rw [map_inv_natCast_smul f R S]

Depends on / 依赖: Rat.cast_def, cast_def, div_eq_mul_inv, map_intCast_smul, map_inv_natCast_smul, mul_smul
-/
theorem map_ratCast_smul [AddCommGroup M] [AddCommGroup M₂] {F : Type*} [FunLike F M M₂]
    [AddMonoidHomClass F M M₂] (f : F) (R S : Type*) [DivisionRing R] [DivisionRing S] [Module R M]
    [Module S M₂] (c : Rat) (x : M) :
    f ((c : R) • x) = (c : S) • f x := by
  rw [Rat.cast_def]; rw [Rat.cast_def]; rw [div_eq_mul_inv]; rw [div_eq_mul_inv]; rw [mul_smul]; rw [mul_smul]; rw [map_intCast_smul f R S]; rw [map_inv_natCast_smul f R S]

/--
theorem `map_nnrat_smul` / 定理 `map_nnrat_smul`

English:
theorem map_nnrat_smul
  statement: [AddCommMonoid M] [AddCommMonoid M₂]
  proof: map_nnratCast_smul f Rat>=0 Rat>=0 c x

中文:
定理 map_nnrat_smul
  结论: [AddCommMonoid M] [AddCommMonoid M₂]
  证明: map_nnratCast_smul f Rat>=0 Rat>=0 c x

Depends on / 依赖: map_nnratCast_smul
-/
theorem map_nnrat_smul [AddCommMonoid M] [AddCommMonoid M₂]
    [_instM : Module Rat>=0 M] [_instM₂ : Module Rat>=0 M₂]
    {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂]
    (f : F) (c : Rat>=0) (x : M) : f (c • x) = c • f x :=
  map_nnratCast_smul f Rat>=0 Rat>=0 c x

/--
theorem `map_rat_smul` / 定理 `map_rat_smul`

English:
theorem map_rat_smul
  statement: [AddCommGroup M] [AddCommGroup M₂]
  proof: map_ratCast_smul f Rat Rat c x

中文:
定理 map_rat_smul
  结论: [AddCommGroup M] [AddCommGroup M₂]
  证明: map_ratCast_smul f Rat Rat c x

Depends on / 依赖: map_ratCast_smul
-/
theorem map_rat_smul [AddCommGroup M] [AddCommGroup M₂]
    [_instM : Module Rat M] [_instM₂ : Module Rat M₂]
    {F : Type*} [FunLike F M M₂] [AddMonoidHomClass F M M₂]
    (f : F) (c : Rat) (x : M) : f (c • x) = c • f x :=
  map_ratCast_smul f Rat Rat c x

/--
Instance `subsingleton_nnrat_module` / 实例 `subsingleton_nnrat_module`

English:
instance subsingleton_nnrat_module
  signature: (E : Type*) [AddCommMonoid E]
  body: ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_nnrat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩

中文:
实例 subsingleton_nnrat_module
  签名: (E : 类型) [AddCommMonoid E]
  定义体: ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_nnrat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, Module, Module.ext, _instM, map_nnrat_smul
-/
instance subsingleton_nnrat_module (E : Type*) [AddCommMonoid E] : Subsingleton (Module Rat>=0 E) :=
  ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_nnrat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩

/--
Instance `subsingleton_rat_module` / 实例 `subsingleton_rat_module`

English:
instance subsingleton_rat_module
  signature: (E : Type*) [AddCommGroup E]
  body: ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_rat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩

中文:
实例 subsingleton_rat_module
  签名: (E : 类型) [AddCommGroup E]
  定义体: ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_rat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, Module, Module.ext, _instM, map_rat_smul
-/
instance subsingleton_rat_module (E : Type*) [AddCommGroup E] : Subsingleton (Module Rat E) :=
  ⟨fun P Q => (Module.ext' P Q) fun r x =>
    map_rat_smul (_instM := P) (_instM₂ := Q) (AddMonoidHom.id E) r x⟩

/--
theorem `nnratCast_smul_eq` / 定理 `nnratCast_smul_eq`

English:
theorem nnratCast_smul_eq
  statement: {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
  proof: map_nnratCast_smul (AddMonoidHom.id E) R S r x

中文:
定理 nnratCast_smul_eq
  结论: {E : 类型} (R S : 类型) [AddCommMonoid E] [DivisionSemiring R]
  证明: map_nnratCast_smul (AddMonoidHom.id E) R S r x

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, map_nnratCast_smul
-/
theorem nnratCast_smul_eq {E : Type*} (R S : Type*) [AddCommMonoid E] [DivisionSemiring R]
    [DivisionSemiring S] [Module R E] [Module S E] (r : Rat>=0) (x : E) : (r : R) • x = (r : S) • x :=
  map_nnratCast_smul (AddMonoidHom.id E) R S r x

/--
theorem `ratCast_smul_eq` / 定理 `ratCast_smul_eq`

English:
theorem ratCast_smul_eq
  statement: {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
  proof: map_ratCast_smul (AddMonoidHom.id E) R S r x

中文:
定理 ratCast_smul_eq
  结论: {E : 类型} (R S : 类型) [AddCommGroup E] [DivisionRing R]
  证明: map_ratCast_smul (AddMonoidHom.id E) R S r x

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, map_ratCast_smul
-/
theorem ratCast_smul_eq {E : Type*} (R S : Type*) [AddCommGroup E] [DivisionRing R]
    [DivisionRing S] [Module R E] [Module S E] (r : Rat) (x : E) : (r : R) • x = (r : S) • x :=
  map_ratCast_smul (AddMonoidHom.id E) R S r x

/--
Instance `IsScalarTower.nnrat` / 实例 `IsScalarTower.nnrat`

English:
instance IsScalarTower.nnrat
  signature: {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
  body: map_nnrat_smul ((smulAddHom R M).flip y) r x

中文:
实例 IsScalarTower.nnrat
  签名: {R : 类型u} {M : 类型v} [Semiring R] [AddCommMonoid M] [Module R M]
  定义体: map_nnrat_smul ((smulAddHom R M).flip y) r x

Depends on / 依赖: map_nnrat_smul, smulAddHom
-/
instance IsScalarTower.nnrat {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
    [Module Rat>=0 R] [Module Rat>=0 M] : IsScalarTower Rat>=0 R M where
  smul_assoc r x y := map_nnrat_smul ((smulAddHom R M).flip y) r x

/--
Instance `IsScalarTower.rat` / 实例 `IsScalarTower.rat`

English:
instance IsScalarTower.rat
  signature: {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
  body: map_rat_smul ((smulAddHom R M).flip y) r x

中文:
实例 IsScalarTower.rat
  签名: {R : 类型u} {M : 类型v} [Ring R] [AddCommGroup M] [Module R M]
  定义体: map_rat_smul ((smulAddHom R M).flip y) r x

Depends on / 依赖: map_rat_smul, smulAddHom
-/
instance IsScalarTower.rat {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
    [Module Rat R] [Module Rat M] : IsScalarTower Rat R M where
  smul_assoc r x y := map_rat_smul ((smulAddHom R M).flip y) r x

/--
lemma `NNRat.cast_smul_eq_nnqsmul` / 引理 `NNRat.cast_smul_eq_nnqsmul`

English:
lemma NNRat.cast_smul_eq_nnqsmul
  statement: (R : Type*) [DivisionSemiring R]
  proof: by
  rw [← one_smul R x]; rw [← smul_assoc]; rw [← smul_assoc]; simp

中文:
引理 NNRat.cast_smul_eq_nnqsmul
  结论: (R : 类型) [DivisionSemiring R]
  证明: by
  rw [← one_smul R x]; rw [← smul_assoc]; rw [← smul_assoc]; simp

Depends on / 依赖: one_smul, smul_assoc
-/
lemma NNRat.cast_smul_eq_nnqsmul (R : Type*) [DivisionSemiring R]
    [MulAction R M] [MulAction Rat>=0 M] [IsScalarTower Rat>=0 R M]
    (q : Rat>=0) (x : M) : (q : R) • x = q • x := by
  rw [← one_smul R x]; rw [← smul_assoc]; rw [← smul_assoc]; simp

/--
lemma `Rat.cast_smul_eq_qsmul` / 引理 `Rat.cast_smul_eq_qsmul`

English:
lemma Rat.cast_smul_eq_qsmul
  statement: (R : Type*) [DivisionRing R]
  proof: by
  rw [← one_smul R x]; rw [← smul_assoc]; rw [← smul_assoc]; simp

中文:
引理 Rat.cast_smul_eq_qsmul
  结论: (R : 类型) [DivisionRing R]
  证明: by
  rw [← one_smul R x]; rw [← smul_assoc]; rw [← smul_assoc]; simp

Depends on / 依赖: one_smul, smul_assoc
-/
lemma Rat.cast_smul_eq_qsmul (R : Type*) [DivisionRing R]
    [MulAction R M] [MulAction Rat M] [IsScalarTower Rat R M]
    (q : Rat) (x : M) : (q : R) • x = q • x := by
  rw [← one_smul R x]; rw [← smul_assoc]; rw [← smul_assoc]; simp

section
variable {α : Type u} {M : Type v}

/--
Instance `SMulCommClass.nnrat` / 实例 `SMulCommClass.nnrat`

English:
instance SMulCommClass.nnrat
  signature: [AddCommMonoid M] [DistribSMul α M] [Module Rat>=0 M]
  body: (map_nnrat_smul (DistribSMul.toAddMonoidHom M x) r y).symm

中文:
实例 SMulCommClass.nnrat
  签名: [AddCommMonoid M] [DistribSMul α M] [Module Rat>=0 M]
  定义体: (map_nnrat_smul (DistribSMul.toAddMonoidHom M x) r y).symm

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_nnrat_smul, toAddMonoidHom
-/
instance SMulCommClass.nnrat [AddCommMonoid M] [DistribSMul α M] [Module Rat>=0 M] :
    SMulCommClass Rat>=0 α M where
  smul_comm r x y := (map_nnrat_smul (DistribSMul.toAddMonoidHom M x) r y).symm

/--
Instance `SMulCommClass.rat` / 实例 `SMulCommClass.rat`

English:
instance SMulCommClass.rat
  signature: [AddCommGroup M] [DistribSMul α M] [Module Rat M]
  body: (map_rat_smul (DistribSMul.toAddMonoidHom M x) r y).symm

中文:
实例 SMulCommClass.rat
  签名: [AddCommGroup M] [DistribSMul α M] [Module Rat M]
  定义体: (map_rat_smul (DistribSMul.toAddMonoidHom M x) r y).symm

Depends on / 依赖: DistribSMul, DistribSMul.toAddMonoidHom, map_rat_smul, toAddMonoidHom
-/
instance SMulCommClass.rat [AddCommGroup M] [DistribSMul α M] [Module Rat M] :
    SMulCommClass Rat α M where
  smul_comm r x y := (map_rat_smul (DistribSMul.toAddMonoidHom M x) r y).symm

/--
Instance `SMulCommClass.nnrat'` / 实例 `SMulCommClass.nnrat'`

English:
instance SMulCommClass.nnrat'
  signature: [AddCommMonoid M] [DistribSMul α M] [Module Rat>=0 M]
  body: SMulCommClass.symm _ _ _

中文:
实例 SMulCommClass.nnrat'
  签名: [AddCommMonoid M] [DistribSMul α M] [Module Rat>=0 M]
  定义体: SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance SMulCommClass.nnrat' [AddCommMonoid M] [DistribSMul α M] [Module Rat>=0 M] :
    SMulCommClass α Rat>=0 M :=
  SMulCommClass.symm _ _ _

/--
Instance `SMulCommClass.rat'` / 实例 `SMulCommClass.rat'`

English:
instance SMulCommClass.rat'
  signature: [AddCommGroup M] [DistribSMul α M] [Module Rat M]
  body: SMulCommClass.symm _ _ _

中文:
实例 SMulCommClass.rat'
  签名: [AddCommGroup M] [DistribSMul α M] [Module Rat M]
  定义体: SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance SMulCommClass.rat' [AddCommGroup M] [DistribSMul α M] [Module Rat M] :
    SMulCommClass α Rat M :=
  SMulCommClass.symm _ _ _

end

variable (M) in
/--
lemma `IsAddTorsionFree.of_module_nnrat` / 引理 `IsAddTorsionFree.of_module_nnrat`

English:
lemma IsAddTorsionFree.of_module_nnrat
  given: [AddCommMonoid M] [Module Rat>=0 M]
  statement: IsAddTorsionFree M where
  proof: by
    simpa [← Nat.cast_smul_eq_nsmul Rat>=0 n, *] using congr((n⁻¹ : Rat>=0) • $hxy)

中文:
引理 IsAddTorsionFree.of_module_nnrat
  条件: [AddCommMonoid M] [Module Rat>=0 M]
  结论: IsAddTorsionFree M where
  证明: by
    simpa [← Nat.cast_smul_eq_nsmul Rat>=0 n, *] using congr((n⁻¹ : Rat>=0) • $hxy)

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul
-/
lemma IsAddTorsionFree.of_module_nnrat [AddCommMonoid M] [Module Rat>=0 M] : IsAddTorsionFree M where
  nsmul_right_injective n hn x y hxy := by
    simpa [← Nat.cast_smul_eq_nsmul Rat>=0 n, *] using congr((n⁻¹ : Rat>=0) • $hxy)

variable (M) in
/--
lemma `IsAddTorsionFree.of_module_rat` / 引理 `IsAddTorsionFree.of_module_rat`

English:
lemma IsAddTorsionFree.of_module_rat
  given: [AddCommGroup M] [Module Rat M]
  statement: IsAddTorsionFree M where
  proof: by
    simpa [← Nat.cast_smul_eq_nsmul Rat n, *] using congr((n⁻¹ : Rat) • $hxy)

中文:
引理 IsAddTorsionFree.of_module_rat
  条件: [AddCommGroup M] [Module Rat M]
  结论: IsAddTorsionFree M where
  证明: by
    simpa [← Nat.cast_smul_eq_nsmul Rat n, *] using congr((n⁻¹ : Rat) • $hxy)

Depends on / 依赖: Nat.cast_smul_eq_nsmul, cast_smul_eq_nsmul
-/
lemma IsAddTorsionFree.of_module_rat [AddCommGroup M] [Module Rat M] : IsAddTorsionFree M where
  nsmul_right_injective n hn x y hxy := by
    simpa [← Nat.cast_smul_eq_nsmul Rat n, *] using congr((n⁻¹ : Rat) • $hxy)
