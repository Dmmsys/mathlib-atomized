/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Convolution

/-!
# Convolution product on bialgebra homs

This file constructs the ring structure on algebra homs `C → A` where `C` is a bialgebra and `A` an
algebra, and also the ring structure on bialgebra homs `C → A` where `C` and `A` are bialgebras.
Both multiplications are given by
```
         |
         μ
| | / \
f * g = f g
| | \ /
         δ
         |
```
diagrammatically, where `μ` stands for multiplication and `δ` for comultiplication.
-/

public section

suppress_compilation

open Algebra Coalgebra Bialgebra TensorProduct WithConv

variable {R A B C : Type*} [CommSemiring R]

namespace AlgHom
variable [CommSemiring A] [CommSemiring B] [Semiring C] [Bialgebra R C] [Algebra R A]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (WithConv <| C ->ₐ[R] A)
  body: toConv (Algebra.ofId R A).comp counitAlgHom R C

中文:
实例 :
  签名: One (WithConv <| C ->ₐ[R] A)
  定义体: toConv (Algebra.ofId R A).comp counitAlgHom R C

Depends on / 依赖: Algebra, Algebra.ofId, counitAlgHom, toConv
-/
instance : One (WithConv <| C ->ₐ[R] A) where
one := toConv (Algebra.ofId R A).comp counitAlgHom R C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (WithConv <| C ->ₐ[R] A)
  body: toConv .comp (lmul' R) .comp (map f.ofConv g.ofConv) comulAlgHom R C

中文:
实例 :
  签名: Mul (WithConv <| C ->ₐ[R] A)
  定义体: toConv .comp (lmul' R) .comp (map f.ofConv g.ofConv) comulAlgHom R C

Depends on / 依赖: comulAlgHom, f.ofConv, g.ofConv, ofConv, toConv
-/
instance : Mul (WithConv <| C ->ₐ[R] A) where
mul f g := toConv .comp (lmul' R) .comp (map f.ofConv g.ofConv) comulAlgHom R C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (WithConv <| C ->ₐ[R] A) Nat
  body: ⟨fun f n => npowRec n f⟩

中文:
实例 :
  签名: Pow (WithConv <| C ->ₐ[R] A) 自然数
  定义体: ⟨fun f n => npowRec n f⟩

Depends on / 依赖: npowRec
-/
instance : Pow (WithConv <| C ->ₐ[R] A) Nat := ⟨fun f n => npowRec n f⟩

/--
lemma `convOne_def` / 引理 `convOne_def`

English:
lemma convOne_def
  statement: 1 = toConv ((Algebra.ofId R A).comp (counitAlgHom R C))
  proof: rfl

中文:
引理 convOne_def
  结论: 1 = toConv ((Algebra.ofId R A).comp (counitAlgHom R C))
  证明: rfl
-/
lemma convOne_def : 1 = toConv ((Algebra.ofId R A).comp (counitAlgHom R C)) := rfl

/--
lemma `convMul_def` / 引理 `convMul_def`

English:
lemma convMul_def
  given: (f g : WithConv <| C ->ₐ[R] A)
  proof: rfl

中文:
引理 convMul_def
  条件: (f g : WithConv <| C ->ₐ[R] A)
  证明: rfl
-/
lemma convMul_def (f g : WithConv <| C ->ₐ[R] A) :
    f * g = toConv (.comp (lmul' R) <| .comp (map f.ofConv g.ofConv) <| comulAlgHom R C) := rfl

/--
lemma `convPow_succ` / 引理 `convPow_succ`

English:
lemma convPow_succ
  given: (f : WithConv <| C ->ₐ[R] A) (n : Nat)
  statement: f ^ (n + 1) = (f ^ n) * f
  proof: rfl

@[simp]

中文:
引理 convPow_succ
  条件: (f : WithConv <| C ->ₐ[R] A) (n : 自然数)
  结论: f ^ (n + 1) = (f ^ n) * f
  证明: rfl

@[simp]
-/
private lemma convPow_succ (f : WithConv <| C ->ₐ[R] A) (n : Nat) : f ^ (n + 1) = (f ^ n) * f := rfl

@[simp]
/--
lemma `convOne_apply` / 引理 `convOne_apply`

English:
lemma convOne_apply
  given: (c : C)
  statement: (1 : WithConv <| C ->ₐ[R] A) c = algebraMap R A (counit c)
  proof: rfl

中文:
引理 convOne_apply
  条件: (c : C)
  结论: (1 : WithConv <| C ->ₐ[R] A) c = algebraMap R A (counit c)
  证明: rfl
-/
lemma convOne_apply (c : C) : (1 : WithConv <| C ->ₐ[R] A) c = algebraMap R A (counit c) := rfl

/--
lemma `convMul_apply` / 引理 `convMul_apply`

English:
lemma convMul_apply
  given: (f g : WithConv <| C ->ₐ[R] A) (c : C)
  proof: by
  simp only [convMul_def, coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply]
  rw [← comp_apply]
  congr 1
  ext <;> simp

@[simp]

中文:
引理 convMul_apply
  条件: (f g : WithConv <| C ->ₐ[R] A) (c : C)
  证明: by
  simp only [convMul_def, coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply]
  rw [← comp_apply]
  congr 1
  ext <;> simp

@[simp]

Depends on / 依赖: Bialgebra, Bialgebra.comulAlgHom_apply, Function, Function.comp_apply, coe_comp, comp_apply, comulAlgHom_apply, convMul_def
-/
lemma convMul_apply (f g : WithConv <| C ->ₐ[R] A) (c : C) :
    (f * g) c = lift f.ofConv g.ofConv (fun _ _ => .all ..) (comul c) := by
  simp only [convMul_def, coe_comp, Function.comp_apply, Bialgebra.comulAlgHom_apply]
  rw [← comp_apply]
  congr 1
  ext <;> simp

@[simp]
/--
lemma `toLinearMap_convOne` / 引理 `toLinearMap_convOne`

English:
lemma toLinearMap_convOne
  statement: toConv (1 : WithConv <| C ->ₐ[R] A).ofConv.toLinearMap = 1
  proof: rfl

@[simp]

中文:
引理 toLinearMap_convOne
  结论: toConv (1 : WithConv <| C ->ₐ[R] A).ofConv.toLinearMap = 1
  证明: rfl

@[simp]
-/
lemma toLinearMap_convOne : toConv (1 : WithConv <| C ->ₐ[R] A).ofConv.toLinearMap = 1 := rfl

@[simp]
/--
lemma `toLinearMap_convMul` / 引理 `toLinearMap_convMul`

English:
lemma toLinearMap_convMul
  given: (f g : WithConv <| C ->ₐ[R] A)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_convMul
  条件: (f g : WithConv <| C ->ₐ[R] A)
  证明: rfl

@[simp]
-/
lemma toLinearMap_convMul (f g : WithConv <| C ->ₐ[R] A) :
    toConv (f * g).ofConv.toLinearMap = toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap :=
  rfl

@[simp]
/--
lemma `toLinearMap_convPow` / 引理 `toLinearMap_convPow`

English:
lemma toLinearMap_convPow
  given: (f : WithConv <| C ->ₐ[R] A)

中文:
引理 toLinearMap_convPow
  条件: (f : WithConv <| C ->ₐ[R] A)
-/
lemma toLinearMap_convPow (f : WithConv <| C ->ₐ[R] A) :
    forall n : Nat, toConv (f ^ n).ofConv.toLinearMap = toConv f.ofConv.toLinearMap ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, toLinearMap_convMul, toLinearMap_convPow, pow_succ]

/--
lemma `convMul_comp_bialgHom_distrib` / 引理 `convMul_comp_bialgHom_distrib`

English:
lemma convMul_comp_bialgHom_distrib
  given: [Bialgebra R B] (f g : WithConv <| C ->ₐ[R] A) (h : B ->ₐc[R] C)
  proof: by
  simp [convMul_def, comp_assoc, Algebra.TensorProduct.map_comp]

中文:
引理 convMul_comp_bialgHom_distrib
  条件: [Bialgebra R B] (f g : WithConv <| C ->ₐ[R] A) (h : B ->ₐc[R] C)
  证明: by
  simp [convMul_def, comp_assoc, Algebra.TensorProduct.map_comp]

Depends on / 依赖: Algebra, Algebra.TensorProduct.map_comp, TensorProduct, comp_assoc, convMul_def, map_comp
-/
lemma convMul_comp_bialgHom_distrib [Bialgebra R B] (f g : WithConv <| C ->ₐ[R] A) (h : B ->ₐc[R] C) :
    AlgHom.comp (f * g).ofConv (h : B ->ₐ[R] C) =
      ofConv (toConv (f.ofConv.comp h) * toConv (g.ofConv.comp h)) := by
  simp [convMul_def, comp_assoc, Algebra.TensorProduct.map_comp]

/--
lemma `comp_convMul_distrib` / 引理 `comp_convMul_distrib`

English:
lemma comp_convMul_distrib
  given: [Algebra R B] (h : A ->ₐ[R] B) (f g : WithConv <| C ->ₐ[R] A)
  proof: by
  apply toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.comp_toLinearMap]; rw [← ofConv_toConv (f * g).ofConv.toLinearMap]; rw [toLinearMap_convMul]
  simp [LinearMap.algHom_comp_convMul_distrib, toLinearMap_convMul]

中文:
引理 comp_convMul_distrib
  条件: [Algebra R B] (h : A ->ₐ[R] B) (f g : WithConv <| C ->ₐ[R] A)
  证明: by
  apply toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.comp_toLinearMap]; rw [← ofConv_toConv (f * g).ofConv.toLinearMap]; rw [toLinearMap_convMul]
  simp [LinearMap.algHom_comp_convMul_distrib, toLinearMap_convMul]

Depends on / 依赖: AlgHom, AlgHom.comp_toLinearMap, LinearMap, LinearMap.algHom_comp_convMul_distrib, WithConv, WithConv.toConv_injective, algHom_comp_convMul_distrib, comp_toLinearMap, ofConv, ofConv.toLinearMap, ofConv_toConv, toConv_injective, toLinearMap, toLinearMap_convMul, toLinearMap_injective
-/
lemma comp_convMul_distrib [Algebra R B] (h : A ->ₐ[R] B) (f g : WithConv <| C ->ₐ[R] A) :
    h.comp (f * g).ofConv = ofConv (toConv (h.comp f.ofConv) * toConv (h.comp g.ofConv)) := by
  apply toLinearMap_injective
  apply WithConv.toConv_injective
  rw [AlgHom.comp_toLinearMap]; rw [← ofConv_toConv (f * g).ofConv.toLinearMap]; rw [toLinearMap_convMul]
  simp [LinearMap.algHom_comp_convMul_distrib, toLinearMap_convMul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monoid (WithConv <| C ->ₐ[R] A)
  body: fast_instance%
  (toConv_injective.comp <| toLinearMap_injective.comp ofConv_injective).monoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

中文:
实例 :
  签名: Monoid (WithConv <| C ->ₐ[R] A)
  定义体: fast_instance%
  (toConv_injective.comp <| toLinearMap_injective.comp ofConv_injective).monoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

Depends on / 依赖: fast_instance
-/
instance : Monoid (WithConv <| C ->ₐ[R] A) := fast_instance%
  (toConv_injective.comp <| toLinearMap_injective.comp ofConv_injective).monoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

variable [IsCocomm R C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoid (WithConv <| C ->ₐ[R] A)
  body: fast_instance%
  (toConv_injective.comp <| toLinearMap_injective.comp ofConv_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

中文:
实例 :
  签名: CommMonoid (WithConv <| C ->ₐ[R] A)
  定义体: fast_instance%
  (toConv_injective.comp <| toLinearMap_injective.comp ofConv_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

Depends on / 依赖: fast_instance
-/
instance : CommMonoid (WithConv <| C ->ₐ[R] A) := fast_instance%
  (toConv_injective.comp <| toLinearMap_injective.comp ofConv_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

end AlgHom

namespace BialgHom
variable [CommSemiring A] [Semiring C] [Bialgebra R A] [Bialgebra R C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (WithConv <| C ->ₐc[R] A)
  body: toConv (unitBialgHom R A).comp counitBialgHom R C

中文:
实例 :
  签名: One (WithConv <| C ->ₐc[R] A)
  定义体: toConv (unitBialgHom R A).comp counitBialgHom R C

Depends on / 依赖: counitBialgHom, toConv, unitBialgHom
-/
instance : One (WithConv <| C ->ₐc[R] A) where
one := toConv (unitBialgHom R A).comp counitBialgHom R C

/--
lemma `convOne_def` / 引理 `convOne_def`

English:
lemma convOne_def
  statement: 1 = toConv ((unitBialgHom R A).comp (counitBialgHom R C))
  proof: rfl

@[simp]

中文:
引理 convOne_def
  结论: 1 = toConv ((unitBialgHom R A).comp (counitBialgHom R C))
  证明: rfl

@[simp]
-/
lemma convOne_def : 1 = toConv ((unitBialgHom R A).comp (counitBialgHom R C)) := rfl

@[simp]
/--
lemma `convOne_apply` / 引理 `convOne_apply`

English:
lemma convOne_apply
  given: (c : C)
  statement: (1 : WithConv <| C ->ₐc[R] A) c = algebraMap R A (counit c)
  proof: rfl

@[simp]

中文:
引理 convOne_apply
  条件: (c : C)
  结论: (1 : WithConv <| C ->ₐc[R] A) c = algebraMap R A (counit c)
  证明: rfl

@[simp]
-/
lemma convOne_apply (c : C) : (1 : WithConv <| C ->ₐc[R] A) c = algebraMap R A (counit c) := rfl

@[simp]
/--
lemma `toLinearMap_convOne` / 引理 `toLinearMap_convOne`

English:
lemma toLinearMap_convOne
  proof: rfl

中文:
引理 toLinearMap_convOne
  证明: rfl
-/
lemma toLinearMap_convOne :
    toConv (SemilinearMapClass.semilinearMap (1 : WithConv <| C ->ₐc[R] A).ofConv) = 1 := rfl

/--
lemma `toAlgHom_convOne` / 引理 `toAlgHom_convOne`

English:
lemma toAlgHom_convOne
  statement: toConv (1 : WithConv <| C ->ₐc[R] A).ofConv.toAlgHom = 1
  proof: rfl

中文:
引理 toAlgHom_convOne
  结论: toConv (1 : WithConv <| C ->ₐc[R] A).ofConv.toAlgHom = 1
  证明: rfl
-/
@[simp] lemma toAlgHom_convOne : toConv (1 : WithConv <| C ->ₐc[R] A).ofConv.toAlgHom = 1 := rfl

variable [IsCocomm R C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (WithConv <| C ->ₐc[R] A)
  body: toConv .comp (mulBialgHom R A) .comp (map f.ofConv g.ofConv) comulBialgHom R C

中文:
实例 :
  签名: Mul (WithConv <| C ->ₐc[R] A)
  定义体: toConv .comp (mulBialgHom R A) .comp (map f.ofConv g.ofConv) comulBialgHom R C

Depends on / 依赖: comulBialgHom, f.ofConv, g.ofConv, mulBialgHom, ofConv, toConv
-/
instance : Mul (WithConv <| C ->ₐc[R] A) where
mul f g := toConv .comp (mulBialgHom R A) .comp (map f.ofConv g.ofConv) comulBialgHom R C

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (WithConv <| C ->ₐc[R] A) Nat
  body: ⟨fun f n => npowRec n f⟩

中文:
实例 :
  签名: Pow (WithConv <| C ->ₐc[R] A) 自然数
  定义体: ⟨fun f n => npowRec n f⟩

Depends on / 依赖: npowRec
-/
instance : Pow (WithConv <| C ->ₐc[R] A) Nat := ⟨fun f n => npowRec n f⟩

/--
lemma `convMul_def` / 引理 `convMul_def`

English:
lemma convMul_def
  given: (f g : WithConv <| C ->ₐc[R] A)
  proof: rfl

中文:
引理 convMul_def
  条件: (f g : WithConv <| C ->ₐc[R] A)
  证明: rfl
-/
lemma convMul_def (f g : WithConv <| C ->ₐc[R] A) :
    f * g =
      toConv (.comp (mulBialgHom R A) <| .comp (map f.ofConv g.ofConv) <| comulBialgHom R C) :=
  rfl

/--
lemma `convPow_succ` / 引理 `convPow_succ`

English:
lemma convPow_succ
  given: (f : WithConv <| C ->ₐc[R] A) (n : Nat)
  statement: f ^ (n + 1) = (f ^ n) * f
  proof: rfl

中文:
引理 convPow_succ
  条件: (f : WithConv <| C ->ₐc[R] A) (n : 自然数)
  结论: f ^ (n + 1) = (f ^ n) * f
  证明: rfl
-/
private lemma convPow_succ (f : WithConv <| C ->ₐc[R] A) (n : Nat) : f ^ (n + 1) = (f ^ n) * f := rfl

-- TODO: Make simp once `SemilinearMapClass.semilinearMap` is not simp nf anymore.
-- @[simp]
/--
lemma `toLinearMap_convMul` / 引理 `toLinearMap_convMul`

English:
lemma toLinearMap_convMul
  given: (f g : WithConv <| C ->ₐc[R] A)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_convMul
  条件: (f g : WithConv <| C ->ₐc[R] A)
  证明: rfl

@[simp]
-/
lemma toLinearMap_convMul (f g : WithConv <| C ->ₐc[R] A) :
    toConv (f * g).ofConv.toLinearMap = toConv f.ofConv.toLinearMap * toConv g.ofConv.toLinearMap :=
  rfl

@[simp]
/--
lemma `toAlgHom_convMul` / 引理 `toAlgHom_convMul`

English:
lemma toAlgHom_convMul
  given: (f g : WithConv <| C ->ₐc[R] A)
  proof: rfl

中文:
引理 toAlgHom_convMul
  条件: (f g : WithConv <| C ->ₐc[R] A)
  证明: rfl
-/
lemma toAlgHom_convMul (f g : WithConv <| C ->ₐc[R] A) :
    toConv (f * g).ofConv.toAlgHom = toConv f.ofConv.toAlgHom * toConv g.ofConv.toAlgHom :=
  rfl

-- TODO: Make simp once `SemilinearMapClass.semilinearMap` is not simp nf anymore.
-- @[simp]
/--
lemma `toLinearMap_convPow` / 引理 `toLinearMap_convPow`

English:
lemma toLinearMap_convPow
  given: (f : WithConv <| C ->ₐc[R] A)

中文:
引理 toLinearMap_convPow
  条件: (f : WithConv <| C ->ₐc[R] A)
-/
lemma toLinearMap_convPow (f : WithConv <| C ->ₐc[R] A) :
    forall n, toConv (f ^ n).ofConv.toLinearMap = toConv f.ofConv.toLinearMap ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, pow_succ, toLinearMap_convMul, toLinearMap_convPow]

@[simp]
/--
lemma `toAlgHom_convPow` / 引理 `toAlgHom_convPow`

English:
lemma toAlgHom_convPow
  given: (f : WithConv <| C ->ₐc[R] A)

中文:
引理 toAlgHom_convPow
  条件: (f : WithConv <| C ->ₐc[R] A)
-/
lemma toAlgHom_convPow (f : WithConv <| C ->ₐc[R] A) :
    forall n, toConv (f ^ n).ofConv.toAlgHom = toConv f.ofConv.toAlgHom ^ n
  | 0 => rfl
  | n + 1 => by simp only [convPow_succ, pow_succ, toAlgHom_convMul, toAlgHom_convPow]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoid (WithConv <| C ->ₐc[R] A)
  body: fast_instance%
  (toConv_injective.comp <| coe_linearMap_injective.comp ofConv_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

中文:
实例 :
  签名: CommMonoid (WithConv <| C ->ₐc[R] A)
  定义体: fast_instance%
  (toConv_injective.comp <| coe_linearMap_injective.comp ofConv_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

Depends on / 依赖: fast_instance
-/
instance : CommMonoid (WithConv <| C ->ₐc[R] A) := fast_instance%
  (toConv_injective.comp <| coe_linearMap_injective.comp ofConv_injective).commMonoid _
    toLinearMap_convOne toLinearMap_convMul toLinearMap_convPow

end BialgHom
